-- Prove2me | solution 1 for P2M_PretorsionImageClosed___comp_cokernelKernelSubobjectArrowIso_hom_4e7f616de0e9
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:24:42.798203+00:00
-- url     : https://prove2.me/submissions/ae47ca01-7ea7-4fb4-a89b-ad4b11944963

module
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Definitions.Def_PretorsionImageClosed_Subobjects_Quotients

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
variable {C : Type*} [Category C] [Abelian C]
namespace PretorsionImageClosed
theorem _root_.solution {X Q : C} (π : X ⟶ Q) [Epi π] :
    cokernel.π (kernelSubobject π).arrow ≫ (cokernelKernelSubobjectArrowIso π).hom = π :=
  cokernel.π_desc _ _ _
end PretorsionImageClosed
