-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.scal_unit_K
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:00:26.193402+00:00
-- url     : https://prove2.me/submissions/590b7b48-d3e7-4727-ae99-b14bad61cc06

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RValue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExpandsAtScale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
variable {G : Over (Spec (CommRingCat.of V))}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (lam : V) (hlam : lam ≠ 0) {W : (pullback G.hom (jK V)).Opens} :
    IsUnit (resTop W (scal (pullback.snd G.hom (jK V) ≫ jK V) lam)) := by
  have hK : IsUnit (algebraMap V (FractionRing V) lam) := by
    have h0 : algebraMap V (FractionRing V) lam ≠ 0 := by
      rw [Ne, ← map_zero (algebraMap V (FractionRing V))]
      exact (IsFractionRing.injective V (FractionRing V)).ne hlam
    exact h0.isUnit
  have e : scal (pullback.snd G.hom (jK V) ≫ jK V) lam =
      (pullback.snd G.hom (jK V)).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom (algebraMap V (FractionRing V) lam)) := by
    simp only [scal, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    congr 1
    have := congrArg (fun f => (CommRingCat.Hom.hom f) lam)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap V (FractionRing V))))
    simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom] at this
    exact this.symm
  rw [e]
  exact (hK.map _).map _ |>.map _
end ReciprocityTheory.ChartRestriction.G.DVR
