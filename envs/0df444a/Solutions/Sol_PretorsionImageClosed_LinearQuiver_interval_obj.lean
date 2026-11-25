-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.interval_obj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:25:27.511872+00:00
-- url     : https://prove2.me/submissions/77a4bb7f-5783-474c-a8ec-6d36845056ef

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
theorem _root_.solution (a d i : Fin n) :
    (interval k a d).obj i = FGModuleCat.of k (intervalSpace k a d i) := rfl
end PretorsionImageClosed.LinearQuiver
