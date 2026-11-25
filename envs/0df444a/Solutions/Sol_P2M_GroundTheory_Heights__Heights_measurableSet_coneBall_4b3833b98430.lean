-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_measurableSet_coneBall_4b3833b98430
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:37:40.291882+00:00
-- url     : https://prove2.me/submissions/5590516b-27d2-4640-b50d-15c278fa079d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ConeBall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound

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
open MvPolynomial MeasureTheory NumberField Matrix
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ)) :
    MeasurableSet (coneBall h W) := by
  have hc : Continuous (h.pointOf) := by
    unfold HermNorm.pointOf
    fun_prop
  have hclosed : IsClosed {y : EuclideanSpace ℂ (Fin n) | ∀ q ∈ W, eval (h.pointOf y) q = 0} := by
    have : {y : EuclideanSpace ℂ (Fin n) | ∀ q ∈ W, eval (h.pointOf y) q = 0} =
        ⋂ q ∈ W, {y | eval (h.pointOf y) q = 0} := by
      ext y; simp
    rw [this]
    exact isClosed_biInter fun q _ => isClosed_eq ((continuous_eval q).comp hc) continuous_const
  have hopen : MeasurableSet (Metric.ball (0 : EuclideanSpace ℂ (Fin n)) 1) :=
    Metric.isOpen_ball.measurableSet
  have := hopen.inter hclosed.measurableSet
  convert this using 1
  ext y
  simp [coneBall, Metric.mem_ball]
end GroundTheory.Heights₂.Heights
