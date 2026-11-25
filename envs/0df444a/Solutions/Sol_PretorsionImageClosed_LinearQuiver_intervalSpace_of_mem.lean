-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.intervalSpace_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:53:11.959485+00:00
-- url     : https://prove2.me/submissions/dd121c12-fc88-493b-a651-c37d5af49041

module
public import Definitions.Def_PretorsionImageClosed_Statement
public import Definitions.Def_PretorsionImageClosed_Modules_FiniteModules
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Interval

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
open PretorsionImageClosed.LinearQuiver
universe u
variable (k : Type u) [Field k]
variable {n : ℕ}
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution {a d i : Fin n} (h : a ≤ i ∧ i ≤ d) :
    intervalSpace k a d i = ⊤ := if_pos h
end PretorsionImageClosed.LinearQuiver
