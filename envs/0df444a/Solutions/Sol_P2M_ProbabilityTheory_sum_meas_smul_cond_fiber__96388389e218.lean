-- Prove2me | solution 1 for P2M_ProbabilityTheory_sum_meas_smul_cond_fiber__96388389e218
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:29:12.814797+00:00
-- url     : https://prove2.me/submissions/646ca5ce-dd42-430e-a2ad-858420a5d48d

module
public import Mathlib.Probability.ConditionalProbability
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_ConditionalProbability

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open ProbabilityTheory
variable {Ω α : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω)
 [MeasurableSpace α] [MeasurableSingletonClass α]
namespace ProbabilityTheory
theorem _root_.solution {X : Ω → α} (hX : Measurable X) [finX : FiniteRange X]
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    ∑ x ∈ finX.toFinset, μ (X ⁻¹' {x}) • μ[|X ← x] = μ := by
  ext E hE
  calc
    _ = ∑ x ∈ finX.toFinset, μ (X ⁻¹' {x} ∩ E) := by
      simp only [Measure.coe_finsetSum, Measure.coe_smul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul]
      simp_rw [mul_comm (μ _), cond_mul_eq_inter (hX (.singleton _))]
    _ = _ := by
      have : ⋃ x ∈ finX.toFinset, X ⁻¹' {x} ∩ E = E := by ext _; simp
      rw [← measure_biUnion_finset _ fun _ _ ↦ (hX (.singleton _)).inter hE, this]
      aesop (add simp [PairwiseDisjoint, Set.Pairwise, Function.onFun, disjoint_left])
end ProbabilityTheory
