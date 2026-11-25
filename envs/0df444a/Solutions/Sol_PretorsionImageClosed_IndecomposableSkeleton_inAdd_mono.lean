-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.inAdd_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:18:04.321167+00:00
-- url     : https://prove2.me/submissions/ae39a27c-2831-435c-b78c-362840a412ad

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitInjective
public import Definitions.Def_PretorsionImageClosed_Subcategories_Biproducts
public import Definitions.Def_PretorsionImageClosed_Statement
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Subcategories

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
theorem _root_.solution {S T : Set ι} (hST : S ⊆ T) {X : FGModuleCat.{w} R} :
    σ.InAdd S X → σ.InAdd T X := by
  rintro ⟨P⟩
  exact ⟨{
    index := P.index, label := P.label, mem := (fun t => hST (P.mem t)), iso := P.iso }⟩
end PretorsionImageClosed.IndecomposableSkeleton
