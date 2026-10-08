-- Prove2me | solution 1 for WassDDRO.Extremal.discreteQ_mem_ball
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T10:39:44.758092+00:00
-- url     : https://prove2.me/submissions/539b9a21-c4db-4e9f-8774-77c6d64b0578

import Definitions.Def_WassDDRO_Extremal_Setting
import Definitions.Def_WassDDRO_Reduction_Setting
set_option autoImplicit false
section
set_option autoImplicit false
namespace WassExtremalCodex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {K N : ℕ}

def toReductionAssumption (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (h : WassDDRO.Extremal.Assumption41 Ξ ℓ) : WassDDRO.Reduction.Assumption41 Ξ ℓ :=
  ⟨h.convex, h.closed, h.ne_top, h.convex_epigraph, h.lsc, h.not_bot_on⟩

theorem maxLoss_eq (ℓ : Fin K → E → EReal) :
    WassDDRO.Extremal.maxLoss ℓ = WassDDRO.Reduction.maxLoss ℓ := rfl

theorem program12f_eq (ε : ℝ) (Ξ : Set E) (ξhat : Fin N → E) (ℓ : Fin K → E → EReal) :
    WassDDRO.Extremal.program12fValue ε Ξ ξhat ℓ = WassDDRO.Reduction.program12fValue ε Ξ ξhat ℓ := rfl

theorem worstCase_eq (ε : ℝ) (Ξ : Set E) (ξhat : Fin N → E) (L : E → EReal) :
    WassDDRO.Extremal.worstCaseExpectation ε Ξ ξhat L = WassDDRO.Reduction.worstCaseExpectation ε Ξ ξhat L := rfl
end WassExtremalCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassExtremalCodex

theorem weighted_rows_probability {Z : Type*} [MeasurableSpace Z] {N K : ℕ}
    (hN : 0 < N) (a : Fin N → Fin K → ℝ) (x : Fin N → Fin K → Z)
    (ha : ∀ i k, 0 ≤ a i k) (hs : ∀ i, ∑ k, a i k = 1) :
    IsProbabilityMeasure ((N : ENNReal)⁻¹ • ∑ i, ∑ k, ENNReal.ofReal (a i k) • Measure.dirac (x i k)) := by
  have hr : ∀ i, (∑ k, ENNReal.ofReal (a i k)) = 1 := by
    intro i
    rw [←ENNReal.ofReal_sum_of_nonneg (fun k _ => ha i k), hs i]
    simp
  constructor
  simp only [Measure.smul_apply, Measure.finsetSum_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
    smul_eq_mul, mul_one, hr, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hN.ne') (ENNReal.natCast_ne_top N)

theorem weighted_rows_ae_support {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {N K : ℕ} (a : Fin N → Fin K → ℝ) (x : Fin N → Fin K → Z) (S : Set Z)
    (hx : ∀ i k, a i k ≠ 0 → x i k ∈ S) :
    ∀ᵐ z ∂((N : ENNReal)⁻¹ • ∑ i, ∑ k, ENNReal.ofReal (a i k) • Measure.dirac (x i k)), z∈S := by
  apply Measure.ae_smul_measure
  rw [ae_finsetSum_measure_iff]
  intro i hi
  rw [ae_finsetSum_measure_iff]
  intro k hk
  by_cases hz : a i k = 0
  · simp [hz]
  · apply Measure.ae_smul_measure
    rw [ae_dirac_eq]
    exact hx i k hz

theorem discreteQ_probability {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N K : ℕ}
    (hN : 0 < N) (Ξ : Set E) (ξhat : Fin N → E) (ε : ℝ)
    (α : Fin N → Fin K → ℝ) (q : Fin N → Fin K → E)
    (h : WassDDRO.Extremal.Feasible13 ε Ξ ξhat α q) :
    IsProbabilityMeasure (WassDDRO.Extremal.discreteQ ξhat α q) :=
  weighted_rows_probability hN α (fun i k => WassDDRO.Extremal.atom13 (ξhat i) (α i k) (q i k)) h.2.2.1 h.2.1

theorem discreteQ_ae_support {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N K : ℕ}
    (Ξ : Set E) (ξhat : Fin N → E) (ε : ℝ)
    (α : Fin N → Fin K → ℝ) (q : Fin N → Fin K → E)
    (h : WassDDRO.Extremal.Feasible13 ε Ξ ξhat α q) :
    ∀ᵐ x ∂WassDDRO.Extremal.discreteQ ξhat α q, x∈Ξ :=
  weighted_rows_ae_support α (fun i k => WassDDRO.Extremal.atom13 (ξhat i) (α i k) (q i k)) Ξ
    (fun i k => (h.2.2.2 i k).2)
end WassExtremalCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassExtremalCodex

theorem weighted_rows_map {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y] {N K : ℕ}
    (a : Fin N → Fin K → ℝ) (x : Fin N → Fin K → Z) (f : Z → Y) (hf : Measurable f) :
    ((N : ENNReal)⁻¹ • ∑ i, ∑ k, ENNReal.ofReal (a i k) • Measure.dirac (x i k)).map f =
      (N : ENNReal)⁻¹ • ∑ i, ∑ k, ENNReal.ofReal (a i k) • Measure.dirac (f (x i k)) := by
  simp only [Measure.map_smul, Measure.map_finset_sum' hf.aemeasurable, Measure.map_dirac' hf]

theorem weighted_rows_lintegral {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {N K : ℕ} (a : Fin N → Fin K → ℝ) (x : Fin N → Fin K → Z) (f : Z → ENNReal) :
    (∫⁻ z, f z ∂((N : ENNReal)⁻¹ • ∑ i, ∑ k, ENNReal.ofReal (a i k) • Measure.dirac (x i k))) =
      (N : ENNReal)⁻¹ * ∑ i, ∑ k, ENNReal.ofReal (a i k) * f (x i k) := by
  simp only [lintegral_smul_measure, lintegral_finsetSum_measure, lintegral_dirac, smul_eq_mul]

theorem atom13_weighted_cost {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (sample q : E) (α : ℝ) (hα : 0 ≤ α) (hz : α = 0 → q = 0) :
    α * ‖WassDDRO.Extremal.atom13 sample α q-sample‖ = ‖q‖ := by
  by_cases h : α=0
  · simp [h,hz h]
  · have hp : 0 < α := lt_of_le_of_ne hα (Ne.symm h)
    have he : WassDDRO.Extremal.atom13 sample α q-sample = -(α⁻¹ • q) := by
      unfold WassDDRO.Extremal.atom13
      abel
    rw [he,norm_neg,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp),←mul_assoc,mul_inv_cancel₀ h,one_mul]

noncomputable def coupling13 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N K : ℕ}
    (ξhat : Fin N → E) (α : Fin N → Fin K → ℝ) (q : Fin N → Fin K → E) : Measure (E×E) :=
  (N : ENNReal)⁻¹ • ∑ i, ∑ k, ENNReal.ofReal (α i k) •
    Measure.dirac (WassDDRO.Extremal.atom13 (ξhat i) (α i k) (q i k),ξhat i)

theorem coupling13_first {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N K : ℕ}
    (ξhat : Fin N → E) (α : Fin N → Fin K → ℝ) (q : Fin N → Fin K → E) :
    (coupling13 ξhat α q).map Prod.fst = WassDDRO.Extremal.discreteQ ξhat α q :=
  weighted_rows_map α _ Prod.fst measurable_fst

theorem coupling13_second {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N K : ℕ}
    (ξhat : Fin N → E) (α : Fin N → Fin K → ℝ) (q : Fin N → Fin K → E)
    (hα : ∀ i k, 0 ≤ α i k) (hs : ∀ i, ∑ k, α i k=1) :
    (coupling13 ξhat α q).map Prod.snd = WassersteinDRO.Duality.empiricalDistribution ξhat := by
  rw [coupling13,weighted_rows_map α _ Prod.snd measurable_snd]
  have hr : ∀ i, (∑ k, ENNReal.ofReal (α i k))=1 := by
    intro i
    rw [←ENNReal.ofReal_sum_of_nonneg (fun k _ => hα i k),hs i]
    simp
  simp only [←Finset.sum_smul,hr,one_smul]
  rfl
end WassExtremalCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassExtremalCodex
open WassDDRO.Extremal WassersteinDRO.Duality

theorem coupling13_cost {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N K : ℕ}
    (hN : 0 < N) (Ξ : Set E) (ξhat : Fin N → E) (ε : ℝ)
    (α : Fin N → Fin K → ℝ) (q : Fin N → Fin K → E)
    (h : Feasible13 ε Ξ ξhat α q) :
    (∫⁻ w : E×E, ENNReal.ofReal ‖w.1-w.2‖ ∂coupling13 ξhat α q) =
      ENNReal.ofReal ((1/(N : ℝ)) * ∑ i, ∑ k, ‖q i k‖) := by
  rw [coupling13,weighted_rows_lintegral]
  have hc : ∀ i k, ENNReal.ofReal (α i k) *
      ENNReal.ofReal ‖atom13 (ξhat i) (α i k) (q i k)-ξhat i‖ = ENNReal.ofReal ‖q i k‖ := by
    intro i k
    rw [←ENNReal.ofReal_mul (h.2.2.1 i k),atom13_weighted_cost _ _ _ (h.2.2.1 i k) (h.2.2.2 i k).1]
  simp only [hc]
  have hi : (N : ENNReal)⁻¹=ENNReal.ofReal (1/(N : ℝ)) := by
    rw [one_div,ENNReal.ofReal_inv_of_pos (by exact_mod_cast hN)]
    simp
  have hs : ∀ i, (∑ k, ENNReal.ofReal ‖q i k‖)=ENNReal.ofReal (∑ k, ‖q i k‖) := by
    intro i
    exact (ENNReal.ofReal_sum_of_nonneg (fun k _ => norm_nonneg (q i k))).symm
  simp_rw [hs]
  rw [hi,←ENNReal.ofReal_sum_of_nonneg (fun i _ => Finset.sum_nonneg (fun k _ => norm_nonneg (q i k))),
    ←ENNReal.ofReal_mul (by positivity)]

theorem discreteQ_mem_ball_full {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N K : ℕ}
    (hN : 0 < N) (Ξ : Set E) (ξhat : Fin N → E) (ε : ℝ)
    (α : Fin N → Fin K → ℝ) (q : Fin N → Fin K → E)
    (h : Feasible13 ε Ξ ξhat α q) :
    discreteQ ξhat α q∈ambiguitySet ε 1 Ξ (empiricalDistribution ξhat) := by
  letI := discreteQ_probability hN Ξ ξhat ε α q h
  refine ⟨measure_univ,?_,?_⟩
  · have hs := discreteQ_ae_support Ξ ξhat ε α q h
    exact ae_iff.mp hs
  · have hm : (coupling13 ξhat α q).map Prod.fst=discreteQ ξhat α q ∧
        (coupling13 ξhat α q).map Prod.snd=empiricalDistribution ξhat :=
      ⟨coupling13_first ξhat α q,coupling13_second ξhat α q h.2.2.1 h.2.1⟩
    have hw : wassersteinDistance 1 (discreteQ ξhat α q) (empiricalDistribution ξhat) ≤
        ∫⁻ w : E×E, ENNReal.ofReal ‖w.1-w.2‖ ∂coupling13 ξhat α q := by
      simp only [wassersteinDistance,one_div_one,ENNReal.rpow_one,Real.rpow_one]
      exact iInf_le_of_le (coupling13 ξhat α q) (iInf_le_of_le hm le_rfl)
    rw [coupling13_cost hN Ξ ξhat ε α q h] at hw
    exact hw.trans (ENNReal.ofReal_le_ofReal h.1)
end WassExtremalCodex

end

set_option autoImplicit false
open WassDDRO.Extremal
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {K N : ℕ} (hN : 0 < N) (Ξ : Set E) (ξhat : Fin N → E) (hξ : ∀ i, ξhat i ∈ Ξ) (ε : ℝ)
    (α : Fin N → Fin K → ℝ) (q : Fin N → Fin K → E) (h : Feasible13 ε Ξ ξhat α q) :
    discreteQ ξhat α q ∈ WassersteinDRO.Duality.ambiguitySet ε 1 Ξ
      (WassersteinDRO.Duality.empiricalDistribution ξhat) := by
  exact WassExtremalCodex.discreteQ_mem_ball_full hN Ξ ξhat ε α q h



#print axioms solution
