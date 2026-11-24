-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_HodgeAlt_alt__Multi_4e0913c07ff2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:28:18.737278+00:00
-- url     : https://prove2.me/submissions/ada65e8a-2362-47f9-892e-ab30e9474993

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOfRTensor

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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open KaehlerDifferential
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeAlt
variable {R V V' W W' : Type} [CommRing R] [AddCommGroup V] [AddCommGroup V'] [AddCommGroup W]
  [AddCommGroup W'] [Module R V] [Module R V'] [Module R W] [Module R W']
namespace GlobalTheory.CompanionTheory.HodgeAlt
theorem _root_.solution (l l' : V →ₗ[R] R) (a b : V) :
    alt l l' (exteriorPower.ιMulti R 2 ![a, b]) = l a * l' b - l' a * l b :=
  (exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _).trans (Matrix.det_fin_two _)
end GlobalTheory.CompanionTheory.HodgeAlt
