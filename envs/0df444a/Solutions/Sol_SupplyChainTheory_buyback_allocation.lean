-- Prove2me | solution 1 for SupplyChainTheory.buyback_allocation
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T01:58:57.236056+00:00
-- url     : https://prove2.me/submissions/b343aeaa-e8a6-47ea-be7c-2e232014bdcc

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

lemma sc_sales_le_Q (D : Measure ℝ) [IsProbabilityMeasure D]
    (hD : Integrable (fun x => x) D) (Q : ℝ) : expSales D Q ≤ Q := by
  unfold expSales
  have := integral_mono (sc_int_min D hD Q) (integrable_const Q) (fun d => min_le_left Q d)
  rw [integral_const] at this
  simpa using this

lemma sc_sales_le_mu (D : Measure ℝ) [IsProbabilityMeasure D]
    (hD : Integrable (fun x => x) D) (Q : ℝ) : expSales D Q ≤ meanDemand D :=
  integral_mono (sc_int_min D hD Q) hD (fun d => min_le_right Q d)

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

lemma sc_chain_lt (P : ContractData) (D : Measure ℝ) [IsProbabilityMeasure D]
    (hD : Integrable (fun x => x) D) (hmu : 0 < meanDemand D) (Q : ℝ) :
    chainProfit P D Q < meanDemand D * (P.r - P.v) := by
  have hS1 := sc_sales_le_Q D hD Q
  have hS2 := sc_sales_le_mu D hD Q
  have hrv := sc_rv P
  have hps := P.ps_nonneg
  have hpr := P.pr_nonneg
  have hcv : 0 < P.c - P.v := by
    have := P.cs_nonneg; have := P.v_lt_cr; simp only [ContractData.c]; linarith
  have hrc : 0 < P.r - P.c := by have := P.profitable; simp only [ContractData.c]; linarith
  have hp : 0 ≤ P.p := by simp only [ContractData.p]; linarith
  set S := expSales D Q
  set μ := meanDemand D
  have e : chainProfit P D Q = (P.r - P.v) * S + P.p * (S - μ) - (P.c - P.v) * Q := by
    simp only [chainProfit]; ring
  rw [e]
  have m1 : P.p * (S - μ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp (by linarith)
  rcases lt_or_ge 0 Q with hQ | hQ
  · have m2 := mul_le_mul_of_nonneg_left hS2 hrv.le
    have m3 := mul_pos hcv hQ
    linarith
  · have m2 := mul_le_mul_of_nonneg_left hS1 hrv.le
    have m3 : (P.r - P.c) * Q ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hrc.le hQ
    have m4 := mul_pos hmu hrv
    have e2 : (P.r - P.v) * Q - (P.c - P.v) * Q = (P.r - P.c) * Q := by ring
    linarith

theorem sc_goal (P : ContractData) (D : Measure ℝ) [IsProbabilityMeasure D]
    (hD : Integrable (fun x => x) D) (hmu : 0 < meanDemand D)
    (hps : 0 < P.ps) (hpr : 0 < P.pr)
    (Q0 : ℝ) (hpos : 0 < chainProfit P D Q0) :
    let πr := fun b => retailerProfit P D (buybackTransfer D (buybackPrice P b) b) Q0
    let πs := fun b => supplierProfit P D (buybackTransfer D (buybackPrice P b) b) Q0
    let b1 := buybackB1 P D Q0
    let b2 := buybackB2 P D Q0
    StrictAntiOn πr (Set.Icc 0 (P.r - P.v + P.pr))
      ∧ StrictMonoOn πs (Set.Icc 0 (P.r - P.v + P.pr))
      ∧ 0 < b1 ∧ b1 < b2 ∧ b2 < P.r - P.v + P.pr
      ∧ (∀ b, 0 ≤ b → b < b1 → πs b < 0 ∧ chainProfit P D Q0 < πr b)
      ∧ πr b1 = chainProfit P D Q0
      ∧ (∀ b, b1 < b → b < b2 → 0 < πr b ∧ 0 < πs b)
      ∧ πs b2 = chainProfit P D Q0
      ∧ (∀ b, b2 < b → b ≤ P.r - P.v + P.pr → πr b < 0 ∧ chainProfit P D Q0 < πs b) := by
  intro πr πs b1 b2
  have hK := sc_K P
  have hrv := sc_rv P
  have hlt := sc_chain_lt P D hD hmu Q0
  set W := chainProfit P D Q0 with hWdef
  set μ := meanDemand D with hμ
  set K := P.r - P.v + P.p with hKdef
  have hp : P.p = P.ps + P.pr := rfl
  have hA : 0 < W + μ * P.p := by rw [hp]; nlinarith
  -- closed forms
  have hform : ∀ b, πr b = (W + μ * P.p) * (P.r - P.v + P.pr - b) / K - μ * P.pr := by
    intro b
    show retailerProfit P D (buybackTransfer D (buybackPrice P b) b) Q0 = _
    rw [(sc_bb_ident P D hD b Q0).1, ← hWdef, ← hμ]
    unfold buybackShare
    rw [← hKdef]
    have hK0 := hK.ne'
    field_simp
    ring
  have hsum : ∀ b, πs b = W - πr b := by
    intro b
    show supplierProfit P D (buybackTransfer D (buybackPrice P b) b) Q0 =
      W - retailerProfit P D (buybackTransfer D (buybackPrice P b) b) Q0
    rw [(sc_bb_ident P D hD b Q0).1, (sc_bb_ident P D hD b Q0).2]
    ring
  have hanti : ∀ a b, a < b → πr b < πr a := by
    intro a b hab
    rw [hform, hform]
    have : (W + μ * P.p) * (P.r - P.v + P.pr - b) < (W + μ * P.p) * (P.r - P.v + P.pr - a) :=
      mul_lt_mul_of_pos_left (by linarith) hA
    have := div_lt_div_of_pos_right this hK
    linarith
  have hb1 : b1 = P.r - P.v + P.pr - K * (W + μ * P.pr) / (W + μ * P.p) := rfl
  have hb2 : b2 = P.r - P.v + P.pr - K * (μ * P.pr) / (W + μ * P.p) := rfl
  have hK0 := hK.ne'
  have hA0 := hA.ne'
  have hr1 : πr b1 = W := by
    rw [hform, hb1]; field_simp; ring
  have hr2 : πr b2 = 0 := by
    rw [hform, hb2]; field_simp; ring
  refine ⟨fun a _ b _ hab => hanti a b hab, fun a _ b _ hab => ?_, ?_, ?_, ?_,
    fun b _ hb => ?_, hr1, fun b hb1' hb2' => ?_, ?_, fun b hb _ => ?_⟩
  · rw [hsum, hsum]; linarith [hanti a b hab]
  · -- 0 < b1
    rw [hb1, sub_pos, div_lt_iff₀ hA]
    have e : (P.r - P.v + P.pr) * (W + μ * P.p) - K * (W + μ * P.pr) =
        P.ps * (μ * (P.r - P.v) - W) := by rw [hKdef, hp]; ring
    have := mul_pos hps (sub_pos.mpr hlt)
    linarith
  · -- b1 < b2
    rw [hb1, hb2, sub_lt_sub_iff_left]
    apply div_lt_div_of_pos_right _ hA
    have : 0 < K * W := mul_pos hK hpos
    nlinarith
  · -- b2 < r - v + pr
    rw [hb2, sub_lt_self_iff]
    exact div_pos (mul_pos hK (mul_pos hmu hpr)) hA
  · have h1 := hanti b b1 hb
    rw [hr1] at h1
    exact ⟨by rw [hsum]; linarith, h1⟩
  · have h1 := hanti b b2 hb2'
    have h2 := hanti b1 b hb1'
    rw [hr2] at h1
    rw [hr1] at h2
    exact ⟨h1, by rw [hsum]; linarith⟩
  · rw [hsum, hr2]; ring
  · have h1 := hanti b2 b hb
    rw [hr2] at h1
    exact ⟨h1, by rw [hsum]; linarith⟩

end SupplyChainTheory

open SupplyChainTheory

theorem solution (P : ContractData) (D : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure D]
    (hD : MeasureTheory.Integrable (fun x => x) D) (hmu : 0 < meanDemand D)
    (hps : 0 < P.ps) (hpr : 0 < P.pr)
    (Q0 : ℝ) (h0 : IsMaxOn (chainProfit P D) Set.univ Q0) (hpos : 0 < chainProfit P D Q0) :
    let πr := fun b => retailerProfit P D (buybackTransfer D (buybackPrice P b) b) Q0
    let πs := fun b => supplierProfit P D (buybackTransfer D (buybackPrice P b) b) Q0
    let b1 := buybackB1 P D Q0
    let b2 := buybackB2 P D Q0
    StrictAntiOn πr (Set.Icc 0 (P.r - P.v + P.pr))
      ∧ StrictMonoOn πs (Set.Icc 0 (P.r - P.v + P.pr))
      ∧ 0 < b1 ∧ b1 < b2 ∧ b2 < P.r - P.v + P.pr
      ∧ (∀ b, 0 ≤ b → b < b1 → πs b < 0 ∧ chainProfit P D Q0 < πr b)
      ∧ πr b1 = chainProfit P D Q0
      ∧ (∀ b, b1 < b → b < b2 → 0 < πr b ∧ 0 < πs b)
      ∧ πs b2 = chainProfit P D Q0
      ∧ (∀ b, b2 < b → b ≤ P.r - P.v + P.pr → πr b < 0 ∧ chainProfit P D Q0 < πs b) := by
  exact sc_goal P D hD hmu hps hpr Q0 hpos
