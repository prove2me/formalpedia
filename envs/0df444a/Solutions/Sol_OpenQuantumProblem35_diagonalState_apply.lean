-- Prove2me | solution 1 for OpenQuantumProblem35.diagonalState_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:00:44.905953+00:00
-- url     : https://prove2.me/submissions/2d6ee264-e2e6-47b2-a9e9-472b187047bb

module
public import Mathlib
public import Definitions.Def_AME125_Defs
public import Theorems.Thm_OpenQuantumProblem35_mkStateVector_apply
attribute [local simp] OpenQuantumProblem35.mkStateVector_apply

set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open OpenQuantumProblem35
namespace OpenQuantumProblem35
theorem _root_.solution {n d : ℕ} (x : Config n d) :
    diagonalState n d x = if IsConstantConfig x then uniformCoeff d else 0 := by
  rw [diagonalState, mkStateVector_apply]
end OpenQuantumProblem35
