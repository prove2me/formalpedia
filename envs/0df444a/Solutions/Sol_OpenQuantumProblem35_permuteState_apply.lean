-- Prove2me | solution 1 for OpenQuantumProblem35.permuteState_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:00:42.503919+00:00
-- url     : https://prove2.me/submissions/c3987ad2-a3a5-4916-b77f-3eba3ec0d9b6

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
theorem _root_.solution {n d : ℕ} (π : Equiv.Perm (Fin n)) (ψ : StateVector n d) (x : Config n d) :
    permuteState π ψ x = ψ (permuteConfig π x) := by
  rw [permuteState, mkStateVector_apply]
end OpenQuantumProblem35
