-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ballProd_subset_polydisc_122db61ad4e0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:26:00.283866+00:00
-- url     : https://prove2.me/submissions/e6c57e8d-0eaf-4582-bbe2-613bd3ccb684

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntSphere
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PMahlerIntegrand

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
open MeasureTheory
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n k : ℕ} (h : HermNorm n) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ (v : Fin n → ℂ) (j : Fin n), ‖v j‖ ≤ C * h.norm v) :
    ballProd h k ⊆ LogInt.polydisc _ C := by
  intro u hu
  simp only [LogInt.polydisc, Set.mem_univ_pi, Metric.mem_closedBall, dist_zero_right]
  intro ij
  exact (hC (fun j => u (ij.1, j)) ij.2).trans (mul_le_of_le_one_right hC0 (hu ij.1).le)
end GroundTheory.Heights₂.Heights
