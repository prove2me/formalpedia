-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.mem_qSet_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:55:15.551794+00:00
-- url     : https://prove2.me/submissions/a8e2b520-bf9c-4498-8e77-b32c54b574ae

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitInjective
public import Definitions.Def_PretorsionImageClosed_Subcategories_Biproducts
public import Definitions.Def_PretorsionImageClosed_Statement
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Subcategories
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_inFac_iff

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open PretorsionImageClosed PretorsionImageClosed.IndecomposableSkeleton
universe u v w
variable {R : Type u} [Ring R] [IsNoetherianRing R] {ι : Type v}
  (σ : IndecomposableSkeleton.{u, v, w} R ι)
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts
namespace PretorsionImageClosed.IndecomposableSkeleton
theorem _root_.solution (S : Set ι) (i : ι) :
    i ∈ σ.qSet S ↔ Statement.Gen (σ.addOf S) (σ.obj i) :=
  σ.inFac_iff S (σ.obj i)
end PretorsionImageClosed.IndecomposableSkeleton
