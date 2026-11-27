-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_metricBound_iff_3bc934b867e5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:11:46.500954+00:00
-- url     : https://prove2.me/submissions/e1bf7cae-f24f-4614-ac97-d0a21e4dfee5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSaturatedFirstCoordinateLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_Height
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_CurveIsOrbit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_NoCommonZeroComplex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_MemMCoordIdealIffOfIsWeightedHomogeneous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermLine_log_div_toGeo_h_fb686777305f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_mem_mcPts_iff_497efdbb0f6c


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
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (P : ArithVariety n) (A A' : HermLine n) (c : ℝ) :
    (∀ z ∈ Geo.mcPts (ι := blockIdx n) P.ideal,
        |Real.log (A.toGeo.h z / A'.toGeo.h z)| ≤ c) ↔
      ∀ z ∈ P.points ℂ, |Real.log (A.metric z) - Real.log (A'.metric z)| ≤ c := by
  constructor
  · intro h z hz
    rw [← HermLine.log_div_toGeo_h A A' hz.1]
    exact h _ ((P.mem_mcPts_iff _).mpr hz)
  · intro h w hw
    have hz := (P.mem_mcPts_iff w).mp hw
    have := h _ hz
    rwa [← HermLine.log_div_toGeo_h A A' hz.1] at this
end GroundTheory.Heights₂.Heights
