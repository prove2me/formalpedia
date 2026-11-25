-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.inFac_iff_trace_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:04:25.006485+00:00
-- url     : https://prove2.me/submissions/7fae29ff-07b9-4664-b926-24459e25ffeb

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
public import Theorems.Thm_PretorsionImageClosed_FGModuleCat_range_eq_top_of_epi

attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.trace_empty
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.reject_empty
section
@[expose] public section
noncomputable section
open Set
open CategoryTheory CategoryTheory.Limits
namespace PretorsionImageClosed.IndecomposableSkeleton
universe u v w
variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)
attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts
private theorem range_le_flattenFinset
    {S : Set ι} {X : FGModuleCat.{w} R}
    (F : Finset (σ.SelectedMapTo S X))
    (f : σ.SelectedMapTo S X) (hf : f ∈ F) :
    LinearMap.range f.map.hom.hom ≤
      LinearMap.range
        (SelectedMapTo.flattenFinset σ F).map.hom.hom := by
  classical
  let outer : FintypeCat.{0} := FintypeCat.of (Fin F.card)
  let pick : outer → σ.SelectedMapTo S X :=
    fun t ↦ (F.equivFin.symm t).1
  let t : outer := F.equivFin ⟨f, hf⟩
  have hpick : pick t = f := by
    simp [pick, t]
  rw [← hpick]
  let flattenIso :
      (⨁ fun t : outer ↦
        σ.sumOver (pick t).index (pick t).label) ≅
        σ.sumOver
          (FintypeCat.of (Σ t : outer, (pick t).index))
          (fun p ↦ (pick p.1).label p.2) :=
    biproductBiproductIso
      (fun t : outer ↦ (pick t).index)
      (fun t s ↦ σ.obj ((pick t).label s))
  let e :
      σ.sumOver (pick t).index (pick t).label ⟶
        σ.sumOver
          (SelectedMapTo.flattenFinset σ F).index
          (SelectedMapTo.flattenFinset σ F).label :=
    biproduct.ι (fun t : outer ↦
      σ.sumOver (pick t).index (pick t).label) t ≫
        flattenIso.hom
  have hfac :
      e ≫ (SelectedMapTo.flattenFinset σ F).map =
        (pick t).map := by
    dsimp only [e, SelectedMapTo.flattenFinset]
    change
      (biproduct.ι (fun t : outer ↦
          σ.sumOver (pick t).index (pick t).label) t ≫
        flattenIso.hom) ≫
          (flattenIso.inv ≫
            biproduct.desc (fun t ↦ (pick t).map)) =
        (pick t).map
    rw [Category.assoc, Iso.hom_inv_id_assoc]
    exact biproduct.ι_desc _ _
  have hlinear := congrArg (fun q ↦ q.hom.hom) hfac
  simp only [FGModuleCat.hom_hom_comp] at hlinear
  rw [← hlinear]
  exact LinearMap.range_comp_le_range e.hom.hom
    (SelectedMapTo.flattenFinset σ F).map.hom.hom
namespace SelectedMapFrom
end SelectedMapFrom
end PretorsionImageClosed.IndecomposableSkeleton
end
end
end

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
theorem _root_.solution (S : Set ι)
    (X : FGModuleCat.{w} R) :
    σ.InFac S X ↔ σ.trace S X = ⊤ := by
  constructor
  · rintro ⟨P⟩
    let f : σ.SelectedMapTo S X :=
      { index := P.index
        label := P.label
        mem := P.mem
        map := P.map }
    letI : Epi P.map := P.epi
    letI : Epi P.map.hom := by
      change Epi
        ((forget₂ (FGModuleCat R) (ModuleCat R)).map P.map)
      infer_instance
    apply top_unique
    rw [← ModuleCat.range_eq_top_of_epi P.map.hom]
    exact le_iSup (fun g : σ.SelectedMapTo S X ↦
      LinearMap.range g.map.hom.hom) f
  · intro htrace
    have hcompact :
        IsCompactElement (⊤ : Submodule R X) := by
      obtain ⟨G, hG⟩ :=
        Module.Finite.fg_top (R := R) (M := X)
      rw [← hG]
      exact Submodule.finset_span_isCompactElement G
    have hle :
        (⊤ : Submodule R X) ≤
          ⨆ f : σ.SelectedMapTo S X,
            LinearMap.range f.map.hom.hom := by
      change (⊤ : Submodule R X) ≤ σ.trace S X
      exact htrace.ge
    let D : Set (Submodule R X) :=
      {M | ∃ F : Finset (σ.SelectedMapTo S X), M = ⨆ f ∈ F, LinearMap.range f.map.hom.hom}
    have hDne : D.Nonempty := ⟨⊥, ∅, by simp⟩
    have hDdir : DirectedOn (· ≤ ·) D := by
      classical
      rintro _ ⟨F₁, rfl⟩ _ ⟨F₂, rfl⟩
      refine ⟨⨆ f ∈ F₁ ∪ F₂, LinearMap.range f.map.hom.hom, ⟨F₁ ∪ F₂, rfl⟩, ?_, ?_⟩
      · exact biSup_mono Finset.subset_union_left
      · exact biSup_mono Finset.subset_union_right
    have hDlub : IsLUB D (⨆ f : σ.SelectedMapTo S X, LinearMap.range f.map.hom.hom) := by
      refine ⟨?_, ?_⟩
      · rintro _ ⟨F, rfl⟩
        exact iSup₂_le fun f _ => le_iSup (fun g : σ.SelectedMapTo S X => LinearMap.range g.map.hom.hom) f
      · intro U hU
        exact iSup_le fun f =>
          (le_iSup₂ (f := fun g (_ : g ∈ ({f} : Finset _)) => LinearMap.range g.map.hom.hom) f
            (Finset.mem_singleton_self f)).trans (hU ⟨{f}, rfl⟩)
    obtain ⟨_, ⟨F, rfl⟩, hF⟩ := hcompact D _ hDne hDdir hDlub hle
    let f := SelectedMapTo.flattenFinset σ F
    have hrange :
        LinearMap.range f.map.hom.hom = ⊤ := by
      apply top_unique
      refine hF.trans ?_
      refine iSup_le fun g ↦ iSup_le fun hg ↦ ?_
      exact range_le_flattenFinset σ F g hg
    refine ⟨{
      index := f.index
      label := f.label
      mem := f.mem
      map := f.map
      epi := ?_ }⟩
    haveI : Epi f.map.hom :=
      (ModuleCat.epi_iff_range_eq_top f.map.hom).mpr hrange
    apply
      (forget₂ (FGModuleCat R) (ModuleCat R)).epi_of_epi_map
    change Epi f.map.hom
    infer_instance
end PretorsionImageClosed.IndecomposableSkeleton
