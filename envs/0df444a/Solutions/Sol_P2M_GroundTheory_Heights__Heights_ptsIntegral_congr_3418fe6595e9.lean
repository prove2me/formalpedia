-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ptsIntegral_congr_3418fe6595e9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:38:46.812982+00:00
-- url     : https://prove2.me/submissions/734058c5-23ff-4846-abee-e8d7d3d82a1a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSaturatedFirstCoordinateLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_Height
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_CurveIsOrbit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_NoCommonZeroComplex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_MemMCoordIdealIffOfIsWeightedHomogeneous

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
theorem _root_.solution (P : Ideal (Geo.MRing κ)) {e : ℕ} (φ : Fin e → ((Σ k, κ k) → ℂ) → ℝ)
    {g g' : ((Σ k, κ k) → ℂ) → ℝ} (hg : ∀ z ∈ Geo.mcPts P, g z = g' z) :
    Geo.ptsIntegral P φ g = Geo.ptsIntegral P φ g' := by
  unfold Geo.ptsIntegral Geo.ptsIntegralAt
  split_ifs with hΨ
  · congr 1
    funext y
    refine finsum_congr fun w ↦ finsum_congr fun _ ↦ ?_
    unfold Geo.sheetDensity
    split_ifs with hγ
    · have hs := hγ.choose_spec
      unfold Geo.IsSheet at hs
      congr 1
      exact hg _ hs.2.self_of_nhds.2.1
    · rfl
  · rfl
end GroundTheory.Heights₂.Heights
