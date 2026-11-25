-- Prove2me | solution 1 for PretorsionImageClosed.Statement.IsPrecokernel.of_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:55:38.14104+00:00
-- url     : https://prove2.me/submissions/0b839aae-c575-4e25-9bef-a1b0583a0b33

module
public import Definitions.Def_PretorsionImageClosed_Subcategories_Basic
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Basic

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits ZeroObject
open PretorsionImageClosed.Statement
variable {C : Type*} [Category C] {Z : ObjectProperty C}
namespace PretorsionImageClosed.Statement
namespace IsPrecokernel
theorem _root_.solution {T X F : C} {u : T ⟶ X} {v v' : X ⟶ F} (h : IsPrecokernel Z u v)
    (e : v = v') : IsPrecokernel Z u v' := e ▸ h
end IsPrecokernel
end PretorsionImageClosed.Statement
