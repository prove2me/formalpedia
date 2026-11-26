-- Prove2me | solution 1 for OpenQuantumProblem35.isConstantConfig_combineFirst_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:08:28.701025+00:00
-- url     : https://prove2.me/submissions/d556397d-e95a-4581-8fef-2b57eae43cd5

module
public import Mathlib
public import Definitions.Def_AME125_Defs
public import Theorems.Thm_OpenQuantumProblem35_mkStateVector_apply
public import Theorems.Thm_OpenQuantumProblem35_permuteState_apply
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_leftIndex
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_rightIndex
public import Theorems.Thm_OpenQuantumProblem35_card_config
public import Theorems.Thm_OpenQuantumProblem35_diagonalState_apply
public import Theorems.Thm_OpenQuantumProblem35_constantCompletion_eq_iff
public import Theorems.Thm_OpenQuantumProblem35_eq_leftIndex_zero_or_eq_rightIndex
attribute [local simp] OpenQuantumProblem35.mkStateVector_apply
attribute [local simp] OpenQuantumProblem35.permuteState_apply
attribute [local simp] OpenQuantumProblem35.combineFirst_leftIndex
attribute [local simp] OpenQuantumProblem35.combineFirst_rightIndex
attribute [local simp] OpenQuantumProblem35.card_config
attribute [local simp] OpenQuantumProblem35.diagonalState_apply

set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open OpenQuantumProblem35
namespace OpenQuantumProblem35
theorem _root_.solution {n d : ℕ} (hn : 1 ≤ n)
    (x : Config 1 d) (z : Config (n - 1) d) :
    IsConstantConfig (combineFirst (n := n) (d := d) 1 hn x z) ↔
      z = constantCompletion (n := n) (d := d) x := by
  rw [constantCompletion_eq_iff]
  constructor
  · intro h i
    have hij :=
      h (rightIndex (m := 1) (n := n) hn i)
        (leftIndex (m := 1) (n := n) hn 0)
    simpa using hij
  · intro hz i j
    rcases eq_leftIndex_zero_or_eq_rightIndex hn i with rfl | ⟨i', rfl⟩
    · rcases eq_leftIndex_zero_or_eq_rightIndex hn j with rfl | ⟨j', rfl⟩
      · simp
      · simpa using (hz j').symm
    · rcases eq_leftIndex_zero_or_eq_rightIndex hn j with rfl | ⟨j', rfl⟩
      · simpa using hz i'
      · simpa using (hz i').trans (hz j').symm
end OpenQuantumProblem35
