-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_volume_null_of_hausdorff_null_a26ea8030678
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:41:11.61391+00:00
-- url     : https://prove2.me/submissions/93e53941-d589-486e-ab46-323e2b9b3884

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeGraphCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeAreaFormula

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
open MeasureTheory Module
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {m : ℕ} {s : Set (EuclideanSpace ℂ (Fin m))}
    (hs : Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) s = 0) : volume s = 0 := by
  have hdim : finrank ℝ (EuclideanSpace ℂ (Fin m)) = 2 * m := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
  have hμ : (Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) : Measure (EuclideanSpace ℂ (Fin m))) =
      Measure.hausdorffMeasure (finrank ℝ (EuclideanSpace ℂ (Fin m)) : ℝ) := by
    rw [hdim]
  rw [hμ] at hs
  exact Measure.absolutelyContinuous_isAddHaarMeasure volume
    (Measure.hausdorffMeasure (finrank ℝ (EuclideanSpace ℂ (Fin m)) : ℝ)) hs
end GroundTheory.Heights₂.Heights
