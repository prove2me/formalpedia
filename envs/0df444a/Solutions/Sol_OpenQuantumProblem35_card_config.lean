-- Prove2me | solution 1 for OpenQuantumProblem35.card_config
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:04:39.963527+00:00
-- url     : https://prove2.me/submissions/15fd8608-4a9e-4843-a43d-b4320dc56cc8

module
public import Mathlib
public import Definitions.Def_AME125_Defs
public import Theorems.Thm_OpenQuantumProblem35_mkStateVector_apply
public import Theorems.Thm_OpenQuantumProblem35_permuteState_apply
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_leftIndex
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_rightIndex
attribute [local simp] OpenQuantumProblem35.mkStateVector_apply
attribute [local simp] OpenQuantumProblem35.permuteState_apply
attribute [local simp] OpenQuantumProblem35.combineFirst_leftIndex
attribute [local simp] OpenQuantumProblem35.combineFirst_rightIndex

set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open OpenQuantumProblem35
namespace OpenQuantumProblem35
theorem _root_.solution (m d : ℕ) : Fintype.card (Config m d) = d ^ m := by
  simp [Config]
end OpenQuantumProblem35
