-- Prove2me | solution 1 for OpenQuantumProblem35.maximallyMixed_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:06:18.411143+00:00
-- url     : https://prove2.me/submissions/87cc1271-5700-45ca-93d8-804495363117

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
theorem _root_.solution {m d : ℕ} (x y : Config m d) :
    maximallyMixed m d x y =
      if x = y then ((Fintype.card (Config m d) : ℂ)⁻¹) else 0 := by
  by_cases h : x = y
  · subst h
    simp [maximallyMixed]
  · simp [maximallyMixed, h]
end OpenQuantumProblem35
