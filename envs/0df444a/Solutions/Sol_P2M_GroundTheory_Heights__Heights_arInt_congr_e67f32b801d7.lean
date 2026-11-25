-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_arInt_congr_e67f32b801d7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:19:22.696818+00:00
-- url     : https://prove2.me/submissions/2728aa85-b4dc-4762-8794-ea34ac168dbc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSaturatedFirstCoordinateLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_Height
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_CurveIsOrbit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_NoCommonZeroComplex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_MemMCoordIdealIffOfIsWeightedHomogeneous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ptsIntegral_congr_3418fe6595e9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable {K : Type*} [Fintype K] {κ : K → Type*} [∀ k, Fintype (κ k)]
omit [∀ k, Fintype (κ k)]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (P : Ideal (Geo.MRing κ)) (s : Geo.MRing κ) {e : ℕ}
    (L : Fin e → Geo.HermLine κ) {A A' : Geo.HermLine κ}
    (hh : ∀ z ∈ Geo.mcPts P, A.h z = A'.h z) : Geo.arInt P s A L = Geo.arInt P s A' L := by
  unfold Geo.arInt
  exact ptsIntegral_congr P _ fun z hz ↦ by rw [Geo.logNorm, Geo.logNorm, hh z hz]
end GroundTheory.Heights₂.Heights
