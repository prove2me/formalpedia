-- Prove2me | solution 1 for ProbabilityTheory.IsUniform.measure_preimage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:27:12.769352+00:00
-- url     : https://prove2.me/submissions/8f118b39-16e6-4a7a-b750-dd8e5f97a020

module
public import Mathlib.Probability.IdentDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_UniformOn
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Uniform
public import Theorems.Thm_ProbabilityTheory_IsUniform_measure_preimage_of_mem

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
namespace _root_.ProbabilityTheory.IsUniform
theorem _root_.solution
    {H : Finset S} (h : IsUniform H X μ) (hX : Measurable X)
    (H' : Set S) : μ (X ⁻¹' H') = (μ univ) * (Nat.card (H' ∩ H : Set S)) / Nat.card H := calc
  _ = μ (X ⁻¹' (H' ∩ H) ∪ X ⁻¹' (H' \ H)) := by simp
  _ = μ (X ⁻¹' (H' ∩ H)) + μ (X ⁻¹' (H' \ H)) :=
    measure_union (Disjoint.preimage X disjoint_inf_sdiff) (by measurability)
  _ = μ (X ⁻¹' (H' ∩ H).toFinite.toFinset) := by
    simp [Set.sdiff_eq_compl_inter, measure_mono_null inter_subset_left h.measure_preimage_compl,
      -preimage_compl]
  _ = μ univ * ∑ __ ∈ (H' ∩ H).toFinite.toFinset, (1 : ENNReal) / Nat.card H := by
    rewrite [← sum_measure_preimage_singleton _ (by measurability), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun _ hx ↦ ?_)
    rw [mul_one_div, h.measure_preimage_of_mem hX ((Finite.mem_toFinset _).mp hx).2]
  _ = (μ univ) * (Nat.card (H' ∩ H).Elem) / Nat.card H := by
    rw [Finset.sum_const, Nat.card_eq_card_finite_toFinset, nsmul_eq_mul, ← mul_assoc,
      mul_one_div]
end _root_.ProbabilityTheory.IsUniform
end ProbabilityTheory
