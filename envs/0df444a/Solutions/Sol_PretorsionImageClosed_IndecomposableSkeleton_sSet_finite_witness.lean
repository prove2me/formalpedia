-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.sSet_finite_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:15:17.69381+00:00
-- url     : https://prove2.me/submissions/bcb900a9-be1b-4f8c-a214-9b70a2291bbc

module
public import Mathlib.CategoryTheory.FintypeCat
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Basic
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Skeleton
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Presentations

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Set
open CategoryTheory CategoryTheory.Limits
open PretorsionImageClosed PretorsionImageClosed.IndecomposableSkeleton
variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)
attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts
namespace PretorsionImageClosed.IndecomposableSkeleton
theorem _root_.solution {S : Set ι} {j : ι}
    (hj : j ∈ σ.sSet S) :
    ∃ T : Set ι, T.Finite ∧ T ⊆ S ∧ j ∈ σ.sSet T := by
  obtain ⟨P⟩ := hj
  let T : Set ι := Set.range P.label
  refine ⟨T, Set.finite_range P.label, ?_, ?_⟩
  · rintro i ⟨t, rfl⟩
    exact P.mem t
  · exact ⟨{
      index := P.index
      label := P.label
      mem := fun t ↦ ⟨t, rfl⟩
      map := P.map
      mono := P.mono }⟩
end PretorsionImageClosed.IndecomposableSkeleton
