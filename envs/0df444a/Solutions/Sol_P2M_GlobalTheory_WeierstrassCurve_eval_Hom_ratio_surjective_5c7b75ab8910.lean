-- Prove2me | solution 1 for P2M_GlobalTheory_WeierstrassCurve_eval_Hom_ratio_surjective_5c7b75ab8910
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:08:17.957081+00:00
-- url     : https://prove2.me/submissions/143c8dfe-cfcf-4ebc-9d9b-3dc77c77ba51

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AwayToSectionFromZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsAffineHomOfIsPullbackSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_SpecMapAwayFnEquivAwayChart
import Theorems.Thm_GlobalTheory_WeierstrassCurve_evalHom_mk


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
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap resG constFn)
open GlobalTheory.ProjFrac GlobalTheory.QCoh.Qcqs GlobalTheory.TangentOrigin
open GlobalTheory
open GlobalTheory.WeierstrassCurve
variable {R : Type} [CommRing R] (W : WeierstrassCurve R)
namespace GlobalTheory.WeierstrassCurve
theorem _root_.solution (i : Fin 3) :
    Function.Surjective (MvPolynomial.eval₂Hom (constOn W (coordOpen W i)) (ratio W i)) := by
  intro a
  obtain ⟨a, rfl⟩ := (awayFnEquiv W i).surjective a
  obtain ⟨n, b, hb, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (grading W) (coord_mem W i) a
  rw [← evalHom_awayCoord]
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  refine ⟨p, ?_⟩
  rw [evalHom_mk]
  have := MvPolynomial.eval₂_comp_left (awayFnEquiv W i).toRingHom (awayConst W i)
    (awayCoord W i) p
  refine Eq.trans ?_ this.symm
  rw [MvPolynomial.coe_eval₂Hom]
  congr 1
  · exact RingHom.ext fun r => (awayFnEquiv_awayConst W i r).symm
  · exact funext fun j => (awayFnEquiv_awayCoord W i j).symm
end GlobalTheory.WeierstrassCurve
