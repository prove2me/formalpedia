-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_volume_real_closedBall_polydisc_62cb1afa7f98
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:50:13.991536+00:00
-- url     : https://prove2.me/submissions/56b740a6-8d06-491a-a0d2-8b39bd03310c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PMollifierLowerBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open MeasureTheory Metric Set
open ReciprocityTheory.AnForm.A
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
theorem _root_.solution {D : ℕ} (x : Fin D → ℂ) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (closedBall x r) = (Real.pi * r ^ 2) ^ D := by
  rw [Measure.real, volume_pi_closedBall x hr]
  simp only [Complex.volume_closedBall, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr]
  simp [mul_comm]
end GroundTheory.Heights₂.Heights.Regular
