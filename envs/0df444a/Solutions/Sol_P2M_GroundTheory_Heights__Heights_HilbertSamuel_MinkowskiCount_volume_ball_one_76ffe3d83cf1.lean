-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_MinkowskiCount_volume_ball_one_76ffe3d83cf1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:55:31.525732+00:00
-- url     : https://prove2.me/submissions/32a3a2b8-7574-4136-bddc-5cd53c04b0a7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMinkowskiCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MeasureTheory Module Metric
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.MinkowskiCount
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.MinkowskiCount
theorem _root_.solution :
    volume (ball (0 : V) 1) = ENNReal.ofReal (unitBallVolume (finrank ℝ V)) := by
  rw [unitBallVolume, ENNReal.ofReal_toReal measure_ball_lt_top.ne,
    ← (stdOrthonormalBasis ℝ V).measurePreserving_repr.measure_preimage
      measurableSet_ball.nullMeasurableSet]
  congr 1
  ext x
  simp
end GroundTheory.Heights₂.Heights.HilbertSamuel.MinkowskiCount
