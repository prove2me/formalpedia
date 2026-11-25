-- Prove2me | solution 1 for PretorsionImageClosed.kernelSubobject_eq_bot_of_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:20:14.474473+00:00
-- url     : https://prove2.me/submissions/62857a7b-5679-40de-a4c9-08dd47238d94

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Subobjects
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_SummandReduction

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement
variable {C : Type*} [Category C] [Abelian C]
namespace PretorsionImageClosed
theorem _root_.solution {X Y : C} (f : X ⟶ Y) [Mono f] : kernelSubobject f = ⊥ :=
  Subobject.mk_eq_bot_iff_zero.2 (kernel.ι_of_mono f)
end PretorsionImageClosed
