-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_secCoord_chart_58c3f1290d13
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:48.573543+00:00
-- url     : https://prove2.me/submissions/58482137-4d3c-4159-914e-09c62150e396

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChowNormFormGeneric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.Vertical
theorem _root_.solution {E : Type*} [Field E] {n e : ℕ} (Q : Ideal (MvPolynomial (Fin n) E))
    (y : Par e n → E) : ∑ j, algebraMap E (SecAlg Q y) (y (.inr j)) * secCoord Q y j = 1 := by
  have h : Ideal.Quotient.mk (secIdeal Q y) (chartForm y) = 1 := by
    rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
    exact Ideal.mem_sup_right (Ideal.subset_span rfl)
  rw [← h, chartForm, linForm, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul]
  rfl
end GroundTheory.Heights₂.Heights.Vertical
