-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.inAdd_obj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:04:09.971658+00:00
-- url     : https://prove2.me/submissions/33f861f7-6c93-4a05-bb7f-07a53c0b4ad1

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
theorem _root_.solution {S : Set ι} {i : ι} (hi : i ∈ S) : σ.InAdd S (σ.obj i) := by
  let a : Fin 1 → ι := fun _ ↦ i
  exact ⟨{
    index := FintypeCat.of (Fin 1)
    label := a
    mem := fun _ ↦ hi
    iso := (biproductUniqueIso fun t : Fin 1 ↦ σ.obj (a t)).symm }⟩
end PretorsionImageClosed.IndecomposableSkeleton
