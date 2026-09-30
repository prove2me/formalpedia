-- Prove2me | solution 1 for SupplyChainTheory.buyback_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T01:58:56.175445+00:00
-- url     : https://prove2.me/submissions/e9d35b9d-2b73-419e-af95-d1fa08cfaecb

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts

open MeasureTheory ProbabilityTheory

namespace SupplyChainTheory

lemma sc_int_min (D : Measure ℝ) [IsProbabilityMeasure D]
    (hD : Integrable (fun x => x) D) (Q : ℝ) : Integrable (fun d => min Q d) D := by
  refine Integrable.mono' ((integrable_const |Q|).add hD.abs)
    (measurable_const.min measurable_id).aestronglyMeasurable
    (Filter.Eventually.of_forall fun d => ?_)
  simp only [Real.norm_eq_abs, Pi.add_apply]
  rcases le_total Q d with h | h
  · rw [min_eq_left h]; linarith [abs_nonneg d]
  · rw [min_eq_right h]; linarith [abs_nonneg Q]

lemma sc_leftover (D : Measure ℝ) [IsProbabilityMeasure D]
    (hD : Integrable (fun x => x) D) (Q : ℝ) : expLeftover D Q = Q - expSales D Q := by
  unfold expLeftover expSales
  have h : ∀ d, max (Q - d) 0 = Q - min Q d := by
    intro d
    rcases le_total Q d with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left (by linarith)]
  simp_rw [h]
  rw [integral_sub (integrable_const Q) (sc_int_min D hD Q), integral_const]
  simp

lemma sc_rv (P : ContractData) : 0 < P.r - P.v := by
  have := P.profitable; have := P.cs_nonneg; have := P.v_lt_cr; linarith

lemma sc_K (P : ContractData) : 0 < P.r - P.v + P.p := by
  have := sc_rv P; have := P.ps_nonneg; have := P.pr_nonneg
  simp only [ContractData.p]; linarith

lemma sc_bb_ident (P : ContractData) (D : Measure ℝ) [IsProbabilityMeasure D]
    (hD : Integrable (fun x => x) D) (b Q : ℝ) :
    retailerProfit P D (buybackTransfer D (buybackPrice P b) b) Q
        = buybackShare P b * chainProfit P D Q
          + meanDemand D * (buybackShare P b * P.p - P.pr)
      ∧ supplierProfit P D (buybackTransfer D (buybackPrice P b) b) Q
        = (1 - buybackShare P b) * chainProfit P D Q
          - meanDemand D * (buybackShare P b * P.p - P.pr) := by
  have hK := (sc_K P).ne'
  unfold retailerProfit supplierProfit buybackTransfer buybackPrice buybackShare chainProfit
  rw [sc_leftover D hD Q]
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

theorem sc_bb_coord (P : ContractData) (D : Measure ℝ) [IsProbabilityMeasure D]
    (hD : Integrable (fun x => x) D) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ P.r - P.v + P.pr) :
    (∀ Q, IsMaxOn (chainProfit P D) Set.univ Q →
        IsMaxOn (retailerProfit P D (buybackTransfer D (buybackPrice P b) b)) Set.univ Q
        ∧ IsMaxOn (supplierProfit P D (buybackTransfer D (buybackPrice P b) b)) Set.univ Q)
      ∧ (b < P.r - P.v + P.pr → ∀ Q,
          IsMaxOn (retailerProfit P D (buybackTransfer D (buybackPrice P b) b)) Set.univ Q
            → IsMaxOn (chainProfit P D) Set.univ Q)
      ∧ (0 < b + P.ps → ∀ Q,
          IsMaxOn (supplierProfit P D (buybackTransfer D (buybackPrice P b) b)) Set.univ Q
            → IsMaxOn (chainProfit P D) Set.univ Q) := by
  have hK := sc_K P
  have hps := P.ps_nonneg
  have hpr := P.pr_nonneg
  have hr := fun Q => (sc_bb_ident P D hD b Q).1
  have hs := fun Q => (sc_bb_ident P D hD b Q).2
  have hl0 : 0 ≤ buybackShare P b := by
    unfold buybackShare; exact div_nonneg (by linarith) hK.le
  have hl1 : 0 ≤ 1 - buybackShare P b := by
    unfold buybackShare
    rw [sub_nonneg, div_le_one hK]
    simp only [ContractData.p]; linarith
  have hs' : ∀ Q, supplierProfit P D (buybackTransfer D (buybackPrice P b) b) Q =
      (1 - buybackShare P b) * chainProfit P D Q
        + -(meanDemand D * (buybackShare P b * P.p - P.pr)) := fun Q => by rw [hs Q]; ring
  have hpos1 : b < P.r - P.v + P.pr → 0 < buybackShare P b := by
    intro hlt; unfold buybackShare; exact div_pos (by linarith) hK
  have hpos2 : 0 < b + P.ps → 0 < 1 - buybackShare P b := by
    intro hlt
    unfold buybackShare
    have : (P.r - P.v + P.pr - b) / (P.r - P.v + P.p) < 1 := by
      rw [div_lt_one hK]; simp only [ContractData.p]; linarith
    linarith
  exact ⟨fun Q hQ => ⟨(sc_max_affine _ _ hr Q).1 hl0 hQ, (sc_max_affine _ _ hs' Q).1 hl1 hQ⟩,
    fun hlt Q hQ => (sc_max_affine _ _ hr Q).2 (hpos1 hlt) hQ,
    fun hlt Q hQ => (sc_max_affine _ _ hs' Q).2 (hpos2 hlt) hQ⟩

end SupplyChainTheory

open SupplyChainTheory

theorem solution (P : ContractData) (D : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure D]
    (hD : MeasureTheory.Integrable (fun x => x) D) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ P.r - P.v + P.pr) :
    (∀ Q, IsMaxOn (chainProfit P D) Set.univ Q →
        IsMaxOn (retailerProfit P D (buybackTransfer D (buybackPrice P b) b)) Set.univ Q
        ∧ IsMaxOn (supplierProfit P D (buybackTransfer D (buybackPrice P b) b)) Set.univ Q)
      ∧ (b < P.r - P.v + P.pr → ∀ Q,
          IsMaxOn (retailerProfit P D (buybackTransfer D (buybackPrice P b) b)) Set.univ Q
            → IsMaxOn (chainProfit P D) Set.univ Q)
      ∧ (0 < b + P.ps → ∀ Q,
          IsMaxOn (supplierProfit P D (buybackTransfer D (buybackPrice P b) b)) Set.univ Q
            → IsMaxOn (chainProfit P D) Set.univ Q) := by
  exact sc_bb_coord P D hD b hb0 hb1
