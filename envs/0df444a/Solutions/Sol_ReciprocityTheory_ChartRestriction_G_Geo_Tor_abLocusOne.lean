-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.abLocusOne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:27:45.970554+00:00
-- url     : https://prove2.me/submissions/293d5ad3-4f88-4b70-91f9-11a8da31c57c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArcSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj

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
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] MvPolynomial.gradedAlgebra
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution : AbLocusOneSt := by
  rintro S G _ hG K _ t ht s ⟨p, rfl⟩ K' _ _ t' ⟨p', hp'⟩
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := t) (g := t') p p' hp'.symm
  let j := (pullback t t').fromSpecResidueField z
  let u := j ≫ pullback.fst t t'
  let u' := j ≫ pullback.snd t t'
  have e : u ≫ t = u' ≫ t' := by simp only [u, u', Category.assoc, pullback.condition]
  have P₁ := (IsPullback.of_hasPullback (pullback.snd G.hom t) u).paste_horiz (IsPullback.of_hasPullback G.hom t)
  have P₂ := (IsPullback.of_hasPullback (pullback.snd G.hom t') u').paste_horiz (IsPullback.of_hasPullback G.hom t')
  rw [← e] at P₂
  have h₂ : UniversallyClosed (pullback.snd (pullback.snd G.hom t') u') := by
    rw [← (P₂.isoIsPullback _ _ P₁).hom_inv_id_assoc (pullback.snd (pullback.snd G.hom t') u'),
      P₂.isoIsPullback_inv_snd]
    infer_instance
  have : Subsingleton (Sp K') := inferInstanceAs (Subsingleton (PrimeSpectrum K'))
  have hu' : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) u' :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have : UniversallyClosed (pullback.snd G.hom t') :=
    MorphismProperty.of_pullback_snd_of_descendsAlong (P := @UniversallyClosed) hu' h₂
  have := hG.separated
  have := hG.smooth
  exact ⟨⟩
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
