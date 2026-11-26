-- Prove2me | solution 1 for PVM.proj_biUnion_finset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:53:24.449375+00:00
-- url     : https://prove2.me/submissions/eb2ad7de-118f-4afa-8837-cb8d4410a675

import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Definitions.Def_Spectral_PVM_Basic
import Theorems.Thm_PVM_proj_union

set_option autoImplicit false
open Function
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace PVM
theorem _root_.solution {I : Type*} (E_pvm : PVM E)
    (s : Finset I) (A : I → Set ℝ) (hmeas : ∀ i ∈ s, MeasurableSet (A i))
    (hpair : (↑s : Set I).PairwiseDisjoint A) :
    E_pvm.proj (⋃ i ∈ (↑s : Set I), A i) = ∑ i ∈ s, E_pvm.proj (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.coe_empty, Set.biUnion_empty, Finset.sum_empty, E_pvm.empty]
  | @insert a s ha ih =>
      have hpair_s : (↑s : Set I).PairwiseDisjoint A :=
        Set.Pairwise.mono (Finset.coe_subset.mpr (Finset.subset_insert a s)) hpair
      have hmeas_s : ∀ i ∈ s, MeasurableSet (A i) :=
        fun i hi => hmeas i (Finset.mem_insert_of_mem hi)
      have hmeas_a : MeasurableSet (A a) :=
        hmeas a (Finset.mem_insert_self a s)
      have hmeas_union : MeasurableSet (⋃ i ∈ (↑s : Set I), A i) :=
        MeasurableSet.biUnion s.countable_toSet (fun i hi => hmeas_s i hi)
      have hadisj : Disjoint (A a) (⋃ i ∈ (↑s : Set I), A i) := by
        rw [Set.disjoint_iUnion_right]
        intro i
        rw [Set.disjoint_iUnion_right]
        intro hi
        exact hpair (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hi)
          (fun hai => ha (hai ▸ hi))
      rw [Finset.coe_insert, Set.biUnion_insert,
        E_pvm.proj_union hmeas_a hmeas_union hadisj,
        Finset.sum_insert ha, ih hmeas_s hpair_s]
end PVM
