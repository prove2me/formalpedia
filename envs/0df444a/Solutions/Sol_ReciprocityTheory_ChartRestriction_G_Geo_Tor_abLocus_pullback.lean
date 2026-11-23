-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.abLocus_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:20:53.423556+00:00
-- url     : https://prove2.me/submissions/6011f71c-1c2a-4944-9e4d-ea54849b3c94

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution (hA : AbLocusOneSt) {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G]
    (hG : IsSemiAbelian G) {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsPullback φ G'.hom G.hom f) (x : S') :
    f x ∈ abLocus G ↔ x ∈ abLocus G' := by
  have key : ∀ (K : Type) [Field K] (t : Sp K ⟶ S'),
      IsProper (pullback.snd G'.hom t) ↔ IsProper (pullback.snd G.hom (t ≫ f)) := by
    intro K _ t
    have hp := (IsPullback.of_hasPullback G'.hom t).paste_horiz h
    have e : pullback.snd G'.hom t = hp.isoPullback.hom ≫ pullback.snd G.hom (t ≫ f) :=
      hp.isoPullback_hom_snd.symm
    rw [e]
    constructor
    · intro hpr
      rw [← Iso.inv_hom_id_assoc hp.isoPullback (pullback.snd G.hom (t ≫ f))]
      infer_instance
    · intro hpr
      infer_instance
  constructor
  · intro hfx
    have hfx' : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ S), f x ∈ Set.range t →
        IsProper (pullback.snd G.hom t) := hfx
    intro K _ _ t hxt
    obtain ⟨p, hp⟩ := hxt
    exact (key K t).2 (hfx' K (t ≫ f) ⟨p, congrArg (fun y => f y) hp⟩)
  · intro hx
    have hx' : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ S'), x ∈ Set.range t →
        IsProper (pullback.snd G'.hom t) := hx
    let κ := AlgebraicClosure (S'.residueField x)
    let t : Sp κ ⟶ S' := Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField x) κ)) ≫
      S'.fromSpecResidueField x
    have hxt : x ∈ Set.range t := by
      have hr := Scheme.range_fromSpecResidueField (X := S') x
      refine ⟨IsLocalRing.closedPoint κ, ?_⟩
      have hm : (S'.fromSpecResidueField x).base
          ((Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField x) κ))).base
            (IsLocalRing.closedPoint κ)) ∈ ({x} : Set S') := hr ▸ ⟨_, rfl⟩
      exact hm
    have hp := (key κ t).1 (hx' κ t hxt)
    obtain ⟨p, hp'⟩ := hxt
    exact hA S G hG κ (t ≫ f) hp ⟨p, congrArg (fun y => f y) hp'⟩
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
