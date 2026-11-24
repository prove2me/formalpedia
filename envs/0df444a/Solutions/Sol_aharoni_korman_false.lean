-- Prove2me | solution 1 for aharoni_korman_false
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:24:56.642083+00:00
-- url     : https://prove2.me/submissions/36acba57-498d-4701-8822-abb174d75f2f

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Setoid.Partition
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.CompleteLattice
import Mathlib.Order.Interval.Set.Infinite
import Definitions.Def_AharoniKorman_ForMathlib_Misc
import Definitions.Def_AharoniKorman_Counterexample
import Theorems.Thm_Hollom_SpinalMap_ext
import Theorems.Thm_Hollom_SpinalMap_toFun_eq_coe
import Theorems.Thm_Hollom_SpinalMap_mem
import Theorems.Thm_Hollom_SpinalMap_idempotent
import Theorems.Thm_Hollom_exists_partition_iff_nonempty_spinalMap
import Theorems.Thm_Hollom_no_spinalMap
attribute [local ext] Hollom.SpinalMap.ext
attribute [local simp] Hollom.SpinalMap.toFun_eq_coe
attribute [local simp] Hollom.SpinalMap.mem
attribute [local simp] Hollom.SpinalMap.idempotent

set_option autoImplicit true
attribute [local aesop 2 simp] Set.subset_def Finset.subset_iff
theorem _root_.solution :
    ¬ ∀ (α : Type) (_ : PartialOrder α),
        (∃ A : Set α, IsAntichain (· ≤ ·) A ∧ A.Infinite) ∨
        (∃ C : Set α, IsChain (· ≤ ·) C ∧
         ∃ S : Set (Set α), Setoid.IsPartition S ∧
          ∀ A ∈ S, IsAntichain (· ≤ ·) A ∧ (A ∩ C).Nonempty) := by
  simp only [not_forall, not_or, not_exists]
  refine ⟨Hollom, inferInstance, ?_, ?_⟩
  · intro A ⟨hA, hA'⟩
    exact hA' (Hollom.no_infinite_antichain hA)
  · rintro C ⟨hC, h⟩
    rw [Hollom.exists_partition_iff_nonempty_spinalMap hC] at h
    obtain ⟨f⟩ := h
    exact Hollom.no_spinalMap hC f
