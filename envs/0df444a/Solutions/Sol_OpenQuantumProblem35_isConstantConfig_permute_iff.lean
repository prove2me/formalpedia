-- Prove2me | solution 1 for OpenQuantumProblem35.isConstantConfig_permute_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:06:31.742808+00:00
-- url     : https://prove2.me/submissions/ea8c1078-ca23-4384-a955-c41bc8a08655

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
theorem _root_.solution {n d : ℕ} (π : Equiv.Perm (Fin n)) (x : Config n d) :
    IsConstantConfig (permuteConfig π x) ↔ IsConstantConfig x := by
  constructor
  · intro h i j
    have hij := h (π.symm i) (π.symm j)
    simpa [permuteConfig] using hij
  · intro h i j
    simpa [permuteConfig] using h (π i) (π j)
end OpenQuantumProblem35
