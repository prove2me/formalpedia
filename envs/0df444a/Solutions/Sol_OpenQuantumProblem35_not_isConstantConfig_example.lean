-- Prove2me | solution 1 for OpenQuantumProblem35.not_isConstantConfig_example
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:09:46.862545+00:00
-- url     : https://prove2.me/submissions/10bf7531-851c-4693-a7a7-f9039356bafd

module
public import Mathlib
public import Definitions.Def_AME125_Defs
public import Theorems.Thm_OpenQuantumProblem35_mkStateVector_apply
public import Theorems.Thm_OpenQuantumProblem35_permuteState_apply
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_leftIndex
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_rightIndex
public import Theorems.Thm_OpenQuantumProblem35_card_config
attribute [local simp] OpenQuantumProblem35.mkStateVector_apply
attribute [local simp] OpenQuantumProblem35.permuteState_apply
attribute [local simp] OpenQuantumProblem35.combineFirst_leftIndex
attribute [local simp] OpenQuantumProblem35.combineFirst_rightIndex
attribute [local simp] OpenQuantumProblem35.card_config

set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open OpenQuantumProblem35
namespace OpenQuantumProblem35
theorem _root_.solution :
    ¬ IsConstantConfig (fun i : Fin 2 => if i = 0 then (0 : Fin 2) else 1) := by
  intro h
  have h01 := h 0 1
  simp at h01
end OpenQuantumProblem35
