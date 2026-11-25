-- Prove2me | solution 1 for P2M_GlobalTheory_ThetaAmple_prod_level__1175cbb17ff8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:34:21.983421+00:00
-- url     : https://prove2.me/submissions/3491543a-ec32-4f3c-8e80-2eeb8af94cd9

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_RelAmpleThetaBundleProjectiveModel
import Theorems.Thm_GlobalTheory_ThetaAmple_level_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaAmple
namespace GlobalTheory.ThetaAmple
theorem _root_.solution {N : ℕ} (w α : ℂ) (F F' : Fin N → ℂ) (hα : α ^ N = eC (-(N : ℂ) * w))
    (hF : ∀ k, F' k = α * eC (-(N : ℂ) * w) * F k) :
    ∏ k, F' k = eC (-((N * (N + 1) : ℕ) : ℂ) * w) * ∏ k, F k := by
  simp only [hF, hα, level_add, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
end GlobalTheory.ThetaAmple
