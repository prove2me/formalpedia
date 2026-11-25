-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_GenSecSeparable_secCoord_form_ecd479731ca9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:23:13.374307+00:00
-- url     : https://prove2.me/submissions/c6bee570-c2d5-4325-88b2-dac5601a083c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChartPointTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsSecPointSeparable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGenSecSeparable

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
open GroundTheory.Heights₂.Heights.Vertical.GenSecSeparable
namespace GroundTheory.Heights₂.Heights.Vertical.GenSecSeparable
theorem _root_.solution {E : Type*} [Field E] {n e : ℕ} (Q : Ideal (MvPolynomial (Fin n) E))
    (y : Par e n → E) (i : Fin e) :
    ∑ j, algebraMap E (SecAlg Q y) (y (.inl (i, j))) * secCoord Q y j = 0 := by
  have h : Ideal.Quotient.mk (secIdeal Q y) (secForm y i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2
      (Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)))
  rw [← h, secForm, linForm, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul]
  rfl
end GroundTheory.Heights₂.Heights.Vertical.GenSecSeparable
