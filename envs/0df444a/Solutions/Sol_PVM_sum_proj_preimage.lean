-- Prove2me | solution 1 for PVM.sum_proj_preimage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:55:20.582298+00:00
-- url     : https://prove2.me/submissions/41da2395-1c37-4181-8b9e-73637f922bc8

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
theorem _root_.solution (E_pvm : PVM E) {β : Type*}
    (f : SimpleFunc ℝ β) (s : Finset β) :
    ∑ y ∈ s, E_pvm.proj (f ⁻¹' {y}) = E_pvm.proj (f ⁻¹' (↑s : Set β)) := by
  classical
  have hmeas : ∀ y ∈ s, MeasurableSet (f ⁻¹' {y}) :=
    fun y _ => f.measurableSet_fiber y
  have hpair : (↑s : Set β).PairwiseDisjoint (fun y => f ⁻¹' {y}) := by
    intro y hy z hz hyz
    change Disjoint (f ⁻¹' {y}) (f ⁻¹' {z})
    rw [Set.disjoint_left]
    intro t hty htz
    change f t = y at hty
    change f t = z at htz
    exact hyz (hty.symm.trans htz)
  have hunion : (⋃ y ∈ (↑s : Set β), f ⁻¹' {y}) = f ⁻¹' (↑s : Set β) := by
    ext t
    constructor
    · intro ht
      rw [Set.mem_iUnion] at ht
      obtain ⟨y, ht⟩ := ht
      rw [Set.mem_iUnion] at ht
      obtain ⟨hy, hty⟩ := ht
      change f t = y at hty
      change f t ∈ (↑s : Set β)
      exact hty.symm ▸ hy
    · intro ht
      change f t ∈ (↑s : Set β) at ht
      rw [Set.mem_iUnion]
      refine ⟨f t, ?_⟩
      rw [Set.mem_iUnion]
      exact ⟨ht, rfl⟩
  rw [← E_pvm.proj_biUnion_finset s (fun y => f ⁻¹' {y}) hmeas hpair, hunion]
end PVM
