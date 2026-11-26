-- Prove2me | solution 1 for OpenQuantumProblem35.diagonalState_combineFirst_two_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:06:45.399664+00:00
-- url     : https://prove2.me/submissions/23d6ef44-b404-4ad9-b14a-9f22ec470163

module
public import Mathlib
public import Definitions.Def_AME125_Defs
public import Theorems.Thm_OpenQuantumProblem35_mkStateVector_apply
public import Theorems.Thm_OpenQuantumProblem35_permuteState_apply
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_leftIndex
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_rightIndex
public import Theorems.Thm_OpenQuantumProblem35_card_config
public import Theorems.Thm_OpenQuantumProblem35_diagonalState_apply
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
theorem _root_.solution {d : ℕ} {x z : Config 2 d}
    (h : x 0 ≠ x 1) :
    diagonalState 4 d (combineFirst (n := 4) (d := d) 2 (by decide) x z) = 0 := by
  have hnot : ¬ IsConstantConfig (combineFirst (n := 4) (d := d) 2 (by decide) x z) := by
    intro hconst
    have hx : x 0 = x 1 := by
      simpa using
        hconst (leftIndex (m := 2) (n := 4) (by decide) 0)
          (leftIndex (m := 2) (n := 4) (by decide) 1)
    exact h hx
  simp [diagonalState_apply, hnot]
end OpenQuantumProblem35
