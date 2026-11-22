-- Prove2me | solution 1 for ProbabilityTheory.isUniform_iff_map_eq_uniformOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:47:40.295984+00:00
-- url     : https://prove2.me/submissions/78035d74-9c46-4e0e-aefd-d9b6c0bed6dc

module
public import Mathlib.Probability.IdentDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_UniformOn
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Uniform
public import Theorems.Thm_ProbabilityTheory_IsUniform_measure_preimage_of_nmem
public import Theorems.Thm_ProbabilityTheory_IsUniform_measure_preimage_of_mem
public import Theorems.Thm_ProbabilityTheory_uniformOn_apply


set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory Measure Set
open scoped ENNReal
open ProbabilityTheory
universe uΩ uS uT uU
variable {Ω : Type uΩ} {S : Type uS} {T : Type uT} [mΩ : MeasurableSpace Ω]
  {X : Ω → S} {Y : Ω → T} {μ : Measure Ω} {H : Set S}
variable [MeasurableSpace S] [DiscreteMeasurableSpace S]
namespace ProbabilityTheory
theorem _root_.solution [Finite H] {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ :
  Measure Ω)
    [Countable S] [IsProbabilityMeasure μ] {U : Ω → S} (hU : Measurable U) :
    IsUniform H U μ ↔ μ.map U = uniformOn H := by
  constructor
  · intro h_unif
    ext A hA
    let Hf := H.toFinite.toFinset
    have h_unif': IsUniform Hf U μ := (Set.Finite.coe_toFinset H.toFinite).symm ▸ h_unif
    let AHf := (A ∩ H).toFinite.toFinset
    rw [uniformOn_apply ‹_›, ← MeasureTheory.Measure.tsum_indicator_apply_singleton _ _ hA]
    classical
    calc ∑' x, Set.indicator A (fun x => (μ.map U) {x}) x
      _ = ∑' x, (if x ∈ (A ∩ H) then (1:ENNReal) / (Nat.card H) else 0) := by
        congr with x
        by_cases h : x ∈ A
        · by_cases h' : x ∈ H <;>
            simp [h, h', Hf, h_unif'.measure_preimage_of_mem hU, h_unif'.measure_preimage_of_nmem,
              map_apply hU (MeasurableSet.singleton x)]
        · simp [h]
      _ = Finset.sum AHf (fun _ ↦ (1:ENNReal) / (Nat.card H)) := by
        rw [tsum_eq_sum (s := (A ∩ H).toFinite.toFinset)]
        · apply Finset.sum_congr (by rfl)
          intro x hx
          simp only [Set.Finite.mem_toFinset, Set.mem_inter_iff, AHf] at hx
          simp [hx]
        simp_all
      _ = Nat.card ↑(H ∩ A) / Nat.card H := by
        simp [Finset.sum_const, Set.inter_comm, AHf, ← Nat.card_eq_card_finite_toFinset]
        rfl
  intro this
  constructor
  · intro x hx y hy
    replace hx : {x} ∩ H = {x} := by simp [hx]
    replace hy : {y} ∩ H = {y} := by simp [hy]
    simp [← map_apply hU (MeasurableSet.singleton _), this, uniformOn_apply, hx, hy, Set.toFinite,
      Set.inter_comm H]
  · rw [← map_apply hU (by measurability), this, uniformOn_apply ‹_›]
    simp
end ProbabilityTheory
