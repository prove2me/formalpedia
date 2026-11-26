-- Prove2me | solution 1 for OpenQuantumProblem35.mkStateVector_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:58:59.621553+00:00
-- url     : https://prove2.me/submissions/7c0a942e-46f4-4c96-9090-3a9fba0fb14e

module
public import Mathlib
public import Definitions.Def_AME125_Defs

set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open OpenQuantumProblem35
namespace OpenQuantumProblem35
theorem _root_.solution {n d : ℕ} (ψ : Config n d → ℂ) (x : Config n d) :
    mkStateVector ψ x = ψ x := rfl
end OpenQuantumProblem35
