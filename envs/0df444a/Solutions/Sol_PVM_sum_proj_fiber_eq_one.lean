-- Prove2me | solution 1 for PVM.sum_proj_fiber_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:55:34.746927+00:00
-- url     : https://prove2.me/submissions/52333b64-da9e-4d6b-9507-3c9ff82e395f

import Definitions.Def_Spectral_PVM_Basic
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Topology.UniformSpace.Dini
import Definitions.Def_Spectral_PVM_Integral
import Theorems.Thm_PVM_proj_biUnion_finset


set_option autoImplicit false
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace PVM
theorem _root_.solution (E_pvm : PVM E) (f : SimpleFunc ℝ ℂ) :
    (∑ z ∈ f.range, E_pvm.proj (f ⁻¹' {z})) = 1 := by
  have hpair : (↑f.range : Set ℂ).PairwiseDisjoint (fun z => f ⁻¹' {z}) := by
    intro z hz w hw hzw
    change Disjoint (f ⁻¹' {z}) (f ⁻¹' {w})
    rw [Set.disjoint_left]
    intro t htz htw
    exact hzw ((Set.mem_singleton_iff.mp htz).symm.trans (Set.mem_singleton_iff.mp htw))
  have hunion : (⋃ z ∈ (↑f.range : Set ℂ), f ⁻¹' {z}) = Set.univ := by
    ext t
    constructor
    · intro ht
      exact Set.mem_univ t
    · intro ht
      rw [Set.mem_iUnion]
      refine ⟨f t, ?_⟩
      rw [Set.mem_iUnion]
      exact ⟨f.mem_range_self t, rfl⟩
  have hmeas : ∀ z ∈ f.range, MeasurableSet (f ⁻¹' {z}) :=
    fun z _ => f.measurableSet_fiber z
  rw [← E_pvm.proj_biUnion_finset f.range (fun z => f ⁻¹' {z}) hmeas hpair,
    hunion, E_pvm.univ]
end PVM
