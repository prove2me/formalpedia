-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.iClosure_splitting_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:07:03.516814+00:00
-- url     : https://prove2.me/submissions/f59ae926-e2f9-4821-b5a5-84b7f048a32c

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Subcategories
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitProjective
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Compact
public import Definitions.Def_PretorsionImageClosed_Realizations_LeastRealization
public import Definitions.Def_PretorsionImageClosed_Length_Modules
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ImageClosure
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_iClosure_isFinitary
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_iClosure_isAntiExchange
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_splitting_eq_extremePoints
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_qClosure_isAntiExchange
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_sClosure_isAntiExchange
public import Theorems.Thm_PretorsionImageClosed_SetClosure_compact_extremePoints_basis
public import Theorems.Thm_PretorsionImageClosed_SetClosure_finiteClosure_isCompactElement
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_ext


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits Set
open PretorsionImageClosed PretorsionImageClosed.IndecomposableSkeleton
universe u v w
variable {R : Type u} [Ring R] [IsNoetherianRing R] {ι : Type v}
  (σ : IndecomposableSkeleton.{u, v, w} R ι)
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts
variable [IsArtinianRing R]
variable [∀ i : ι, IsArtinianRing (Module.End R (σ.obj i))]
namespace PretorsionImageClosed.IndecomposableSkeleton
theorem _root_.solution {Z : Statement.Subcategory (FGModuleCat.{w} R)}
    (hZ : Z.IsImageClosed) (hfin : (σ.indOf Z).Finite) :
    σ.iClosure
      {x ∈ σ.indOf Z | IsSplittingProjective Z (σ.obj x) ∨ IsSplittingInjective Z (σ.obj x)} =
      σ.indOf Z := by
  have hC := (σ.isImageClosed_iff_isClosed_indOf Z).1 hZ
  have hcompact : IsCompactElement (⟨σ.indOf Z, hC⟩ : σ.iClosure.Closeds) := by
    have := SetClosure.finiteClosure_isCompactElement (σ.iClosure_isFinitary) hfin
    have heq : σ.iClosure.toCloseds (σ.indOf Z) = ⟨σ.indOf Z, hC⟩ := Subtype.ext hC.closure_eq
    rwa [heq] at this
  have h := SetClosure.compact_extremePoints_basis σ.iClosure_isFinitary
    (σ.iClosure_isAntiExchange (σ.qClosure_isAntiExchange) (σ.sClosure_isAntiExchange)) hcompact
  rw [splitting_eq_extremePoints]
  exact h.2.1
end PretorsionImageClosed.IndecomposableSkeleton
