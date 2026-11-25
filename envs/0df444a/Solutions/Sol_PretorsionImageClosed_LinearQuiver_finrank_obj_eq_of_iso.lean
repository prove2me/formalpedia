-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.finrank_obj_eq_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:01:50.703021+00:00
-- url     : https://prove2.me/submissions/494b323d-fa25-4b2b-93a5-b5555e8c866d

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Decomposition
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Indecomposables

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution {X Y : Statement.LinRep k n} (e : X ≅ Y) (i : Fin n) :
    Module.finrank k (X.obj i) = Module.finrank k (Y.obj i) :=
  LinearEquiv.finrank_eq (FGModuleCat.isoToLinearEquiv (e.app i))
end PretorsionImageClosed.LinearQuiver
