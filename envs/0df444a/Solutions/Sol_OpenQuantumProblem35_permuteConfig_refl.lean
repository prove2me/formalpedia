-- Prove2me | solution 1 for OpenQuantumProblem35.permuteConfig_refl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:00:50.032579+00:00
-- url     : https://prove2.me/submissions/690897d0-5d51-41ee-9755-2d413169be5d

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
    permuteConfig (Equiv.refl (Fin n)) x = x := by
  ext i
  simp [permuteConfig]
end OpenQuantumProblem35
