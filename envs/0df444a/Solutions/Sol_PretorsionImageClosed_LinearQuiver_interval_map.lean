-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.interval_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:57:38.051805+00:00
-- url     : https://prove2.me/submissions/f623011b-17e2-4cf5-b03c-f61fe7dc2ad0

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
theorem _root_.solution (a d : Fin n) {i j : Fin n} (f : i ⟶ j) :
    (interval k a d).map f =
      FGModuleCat.ofHom (inclusionOrZero k (intervalSpace k a d i) (intervalSpace k a d j)) := rfl
end PretorsionImageClosed.LinearQuiver
