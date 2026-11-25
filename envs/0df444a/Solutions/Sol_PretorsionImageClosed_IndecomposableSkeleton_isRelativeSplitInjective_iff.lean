-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.isRelativeSplitInjective_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T07:53:19.651269+00:00
-- url     : https://prove2.me/submissions/c8185d5e-3d33-49be-a75c-01143cad0caf

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Subcategories
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitProjective
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Compact
public import Definitions.Def_PretorsionImageClosed_Realizations_LeastRealization
public import Definitions.Def_PretorsionImageClosed_Length_Modules
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ImageClosure
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_prop_iff_inAdd_indOf
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPrekernel_mono
public import Theorems.Thm_PretorsionImageClosed_Statement_IsTrivial_mono
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_prop_biproduct


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
omit [IsArtinianRing R]
namespace PretorsionImageClosed.IndecomposableSkeleton
theorem _root_.solution (Z : Statement.Subcategory (FGModuleCat.{w} R)) (x : ι) :
    σ.IsRelativeSplitInjective (σ.indOf Z) x ↔ IsSplittingInjective Z (σ.obj x) := by
  constructor
  · intro h N i hN hi
    have hN' := (σ.prop_iff_inAdd_indOf Z N).1 hN
    obtain ⟨P⟩ := hN'
    obtain ⟨s⟩ := h {
      index := P.index
      label := P.label
      mem := P.mem
      map := i ≫ P.iso.hom
      mono := mono_comp _ _ }
    exact ⟨⟨P.iso.hom ≫ s.retraction, by rw [← Category.assoc]; exact s.id⟩⟩
  · intro h P
    letI : Fintype P.index := FintypeCat.fintype
    exact (h P.map (Z.prop_biproduct _ fun t => P.mem t) P.mono).exists_splitMono.some
      |> Nonempty.intro
end PretorsionImageClosed.IndecomposableSkeleton
