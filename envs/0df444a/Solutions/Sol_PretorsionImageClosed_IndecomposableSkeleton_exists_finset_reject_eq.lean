-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.exists_finset_reject_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:38:18.48875+00:00
-- url     : https://prove2.me/submissions/1d2b0730-febb-403e-8fb6-31ce4f87642e

module
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.CompactlyGenerated.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Presentations
public import Definitions.Def_PretorsionImageClosed_Modules_FiniteModules
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ModuleTraces
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_trace_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_qSet_empty
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.trace_empty
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.reject_empty
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.qSet_empty

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Set
open CategoryTheory CategoryTheory.Limits
open PretorsionImageClosed PretorsionImageClosed.IndecomposableSkeleton
universe u v w
variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)
attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts
namespace PretorsionImageClosed.IndecomposableSkeleton
theorem _root_.solution
    (S : Set ι) (X : FGModuleCat.{w} R)
    (hX : IsFiniteLength R X) :
    ∃ F : Finset (σ.SelectedMapFrom S X),
      (⨅ f ∈ F, LinearMap.ker f.map.hom.hom) =
        σ.reject S X := by
  classical
  have hNA := isFiniteLength_iff_isNoetherian_isArtinian.mp hX
  letI : IsArtinian R X := hNA.2
  let S_fin : Set (Submodule R X) :=
    {M | ∃ F : Finset (σ.SelectedMapFrom S X), M = ⨅ f ∈ F, LinearMap.ker f.map.hom.hom}
  have hne : S_fin.Nonempty := ⟨⊤, ∅, by simp⟩
  obtain ⟨M₀, ⟨F, rfl⟩, hmin⟩ := (wellFounded_lt (α := Submodule R X)).has_min S_fin hne
  refine ⟨F, le_antisymm ?_ ?_⟩
  · change (⨅ f ∈ F, LinearMap.ker f.map.hom.hom) ≤ ⨅ f : σ.SelectedMapFrom S X, LinearMap.ker f.map.hom.hom
    rw [le_iInf_iff]
    intro g
    have hmem : (⨅ f ∈ insert g F, LinearMap.ker f.map.hom.hom) ∈ S_fin := ⟨insert g F, rfl⟩
    have hle : (⨅ f ∈ insert g F, LinearMap.ker f.map.hom.hom) ≤ (⨅ f ∈ F, LinearMap.ker f.map.hom.hom) := by
      rw [Finset.iInf_insert]; exact inf_le_right
    have heq : (⨅ f ∈ insert g F, LinearMap.ker f.map.hom.hom) = (⨅ f ∈ F, LinearMap.ker f.map.hom.hom) :=
      hle.eq_or_lt.resolve_right (hmin _ hmem)
    rw [← heq, Finset.iInf_insert]
    exact inf_le_left
  rw [le_iInf_iff]
  intro f
  rw [le_iInf_iff]
  intro hf
  exact iInf_le_of_le f le_rfl
end PretorsionImageClosed.IndecomposableSkeleton
