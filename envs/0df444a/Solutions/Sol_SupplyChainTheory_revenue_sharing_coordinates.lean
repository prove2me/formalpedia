-- Prove2me | solution 1 for SupplyChainTheory.revenue_sharing_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T01:58:56.65499+00:00
-- url     : https://prove2.me/submissions/9a77f6cf-56cb-400d-8f2f-c5b3b81517f6

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts

open MeasureTheory ProbabilityTheory

namespace SupplyChainTheory

lemma sc_rv (P : ContractData) : 0 < P.r - P.v := by
  have := P.profitable; have := P.cs_nonneg; have := P.v_lt_cr; linarith

lemma sc_K (P : ContractData) : 0 < P.r - P.v + P.p := by
  have := sc_rv P; have := P.ps_nonneg; have := P.pr_nonneg
  simp only [ContractData.p]; linarith

lemma sc_rs_ident (P : ContractData) (D : Measure ℝ) (phi Q : ℝ) :
    retailerProfit P D (revenueShareTransfer P D (revenueSharePrice P phi) phi) Q
        = revenueShareLambda P phi * chainProfit P D Q
          + meanDemand D * (revenueShareLambda P phi * P.p - P.pr)
      ∧ supplierProfit P D (revenueShareTransfer P D (revenueSharePrice P phi) phi) Q
        = (1 - revenueShareLambda P phi) * chainProfit P D Q
          - meanDemand D * (revenueShareLambda P phi * P.p - P.pr) := by
  have hK := (sc_K P).ne'
  unfold retailerProfit supplierProfit revenueShareTransfer revenueSharePrice
    revenueShareLambda chainProfit
  simp only [ContractData.c, ContractData.p] at hK ⊢
  constructor <;> field_simp <;> ring

lemma sc_max_affine {g h : ℝ → ℝ} (a k : ℝ) (hg : ∀ Q, g Q = a * h Q + k) (Q : ℝ) :
    (0 ≤ a → IsMaxOn h Set.univ Q → IsMaxOn g Set.univ Q) ∧
      (0 < a → IsMaxOn g Set.univ Q → IsMaxOn h Set.univ Q) := by
  refine ⟨fun ha hmax y _ => ?_, fun ha hmax y _ => ?_⟩
  · show g y ≤ g Q
    rw [hg, hg]
    have := hmax (Set.mem_univ y)
    have := mul_le_mul_of_nonneg_left this ha
    linarith
  · show h y ≤ h Q
    have h1 : g y ≤ g Q := hmax (Set.mem_univ y)
    rw [hg, hg] at h1
    have h2 : a * h y ≤ a * h Q := by linarith
    exact le_of_mul_le_mul_left h2 ha

theorem sc_rs_coord (P : ContractData) (D : Measure ℝ) [IsProbabilityMeasure D]
    (hD : Integrable (fun x => x) D) (phi : ℝ) (h0 : 0 ≤ phi) (h1 : phi ≤ 1) :
    (∀ Q, IsMaxOn (chainProfit P D) Set.univ Q →
        IsMaxOn (retailerProfit P D (revenueShareTransfer P D (revenueSharePrice P phi) phi))
          Set.univ Q
        ∧ IsMaxOn (supplierProfit P D (revenueShareTransfer P D (revenueSharePrice P phi) phi))
          Set.univ Q)
      ∧ (0 < phi * (P.r - P.v) + P.pr → ∀ Q,
          IsMaxOn (retailerProfit P D (revenueShareTransfer P D (revenueSharePrice P phi) phi))
            Set.univ Q → IsMaxOn (chainProfit P D) Set.univ Q)
      ∧ (phi * (P.r - P.v) + P.pr < P.r - P.v + P.p → ∀ Q,
          IsMaxOn (supplierProfit P D (revenueShareTransfer P D (revenueSharePrice P phi) phi))
            Set.univ Q → IsMaxOn (chainProfit P D) Set.univ Q) := by
  have hK := sc_K P
  have hrv := sc_rv P
  have hps := P.ps_nonneg
  have hpr := P.pr_nonneg
  have hr := fun Q => (sc_rs_ident P D phi Q).1
  have hs := fun Q => (sc_rs_ident P D phi Q).2
  have hl0 : 0 ≤ revenueShareLambda P phi := by
    unfold revenueShareLambda; exact div_nonneg (by nlinarith) hK.le
  have hl1 : 0 ≤ 1 - revenueShareLambda P phi := by
    unfold revenueShareLambda
    rw [sub_nonneg, div_le_one hK]
    simp only [ContractData.p]; nlinarith
  have hs' : ∀ Q, supplierProfit P D (revenueShareTransfer P D (revenueSharePrice P phi) phi) Q =
      (1 - revenueShareLambda P phi) * chainProfit P D Q
        + -(meanDemand D * (revenueShareLambda P phi * P.p - P.pr)) := fun Q => by rw [hs Q]; ring
  have hpos1 : 0 < phi * (P.r - P.v) + P.pr → 0 < revenueShareLambda P phi := by
    intro hlt; unfold revenueShareLambda; exact div_pos hlt hK
  have hpos2 : phi * (P.r - P.v) + P.pr < P.r - P.v + P.p → 0 < 1 - revenueShareLambda P phi := by
    intro hlt
    unfold revenueShareLambda
    have : (phi * (P.r - P.v) + P.pr) / (P.r - P.v + P.p) < 1 := by rw [div_lt_one hK]; exact hlt
    linarith
  exact ⟨fun Q hQ => ⟨(sc_max_affine _ _ hr Q).1 hl0 hQ, (sc_max_affine _ _ hs' Q).1 hl1 hQ⟩,
    fun hlt Q hQ => (sc_max_affine _ _ hr Q).2 (hpos1 hlt) hQ,
    fun hlt Q hQ => (sc_max_affine _ _ hs' Q).2 (hpos2 hlt) hQ⟩

end SupplyChainTheory

open SupplyChainTheory

theorem solution (P : ContractData) (D : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure D]
    (hD : MeasureTheory.Integrable (fun x => x) D) (phi : ℝ) (h0 : 0 ≤ phi) (h1 : phi ≤ 1) :
    (∀ Q, IsMaxOn (chainProfit P D) Set.univ Q →
        IsMaxOn (retailerProfit P D (revenueShareTransfer P D (revenueSharePrice P phi) phi))
          Set.univ Q
        ∧ IsMaxOn (supplierProfit P D (revenueShareTransfer P D (revenueSharePrice P phi) phi))
          Set.univ Q)
      ∧ (0 < phi * (P.r - P.v) + P.pr → ∀ Q,
          IsMaxOn (retailerProfit P D (revenueShareTransfer P D (revenueSharePrice P phi) phi))
            Set.univ Q → IsMaxOn (chainProfit P D) Set.univ Q)
      ∧ (phi * (P.r - P.v) + P.pr < P.r - P.v + P.p → ∀ Q,
          IsMaxOn (supplierProfit P D (revenueShareTransfer P D (revenueSharePrice P phi) phi))
            Set.univ Q → IsMaxOn (chainProfit P D) Set.univ Q) := by
  exact sc_rs_coord P D hD phi h0 h1
