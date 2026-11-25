-- Prove2me | solution 1 for P2M_GlobalTheory_CoordFn_surjective_eval_Hom_awayCoord_b9296fda01ae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:45:21.484388+00:00
-- url     : https://prove2.me/submissions/394e5547-c6d6-4846-a048-d9e15d53f15a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsIsoAppLEOfOpensRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw
open GlobalTheory GlobalTheory.CoordFn
namespace GlobalTheory.CoordFn
theorem _root_.solution {R : Type} [CommRing R] (W : WeierstrassCurve R)
    (i : Fin 3) :
    Function.Surjective (MvPolynomial.eval₂Hom (awayConst W i) (awayCoord W i)) := by
  intro x
  obtain ⟨n, a, ha, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (grading W) (coord_mem W i) x
  rw [← evalHom_awayCoord]
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact ⟨p, rfl⟩
end GlobalTheory.CoordFn
