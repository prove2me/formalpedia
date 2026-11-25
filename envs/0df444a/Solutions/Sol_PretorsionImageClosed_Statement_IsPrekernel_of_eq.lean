-- Prove2me | solution 1 for PretorsionImageClosed.Statement.IsPrekernel.of_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:54:23.473863+00:00
-- url     : https://prove2.me/submissions/899f14e2-6708-4073-80d4-ba465f6e9fb5

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
namespace IsPrekernel
theorem _root_.solution {T X F : C} {u u' : T ⟶ X} {v : X ⟶ F} (h : IsPrekernel Z u v)
    (e : u = u') : IsPrekernel Z u' v := e ▸ h
end IsPrekernel
end PretorsionImageClosed.Statement
