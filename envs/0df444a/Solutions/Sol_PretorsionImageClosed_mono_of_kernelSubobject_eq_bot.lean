-- Prove2me | solution 1 for PretorsionImageClosed.mono_of_kernelSubobject_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:22:57.608652+00:00
-- url     : https://prove2.me/submissions/89497473-06e2-4315-a85e-9547db44b421

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
theorem _root_.solution {X Y : C} (f : X ⟶ Y) (h : kernelSubobject f = ⊥) : Mono f :=
  Abelian.mono_of_kernel_ι_eq_zero _ (Subobject.mk_eq_bot_iff_zero.1 h)
end PretorsionImageClosed
