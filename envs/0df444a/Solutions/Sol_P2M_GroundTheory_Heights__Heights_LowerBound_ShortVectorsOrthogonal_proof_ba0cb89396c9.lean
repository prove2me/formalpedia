-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBound_ShortVectorsOrthogonal_proof_ba0cb89396c9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:08:03.861442+00:00
-- url     : https://prove2.me/submissions/0c718f62-251c-486a-812e-6cf68f7f48b2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_PShortVectorsOrthogonal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBound_ShortVectorsOrthogonal_rpow_neg_half_mul_self_3367405b2c2d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBound
open Real
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.LowerBound
namespace ShortVectorsOrthogonal
theorem _root_.solution : ShortVectorsOrthogonal.Statement := by
  intro L _ len E a vr h v w hv hw
  set r := vr ^ (-(1 / 2 : ℝ)) with hr
  have hvr := h.vr_pos
  have hr_pos : 0 < r := Real.rpow_pos_of_pos hvr _
  have hrr : vr * (r * r) = 1 := by
    rw [hr, ShortVectorsOrthogonal.rpow_neg_half_mul_self hvr, mul_inv_cancel₀ hvr.ne']
  have hv0 := h.len_nonneg v
  have hw0 := h.len_nonneg w
  have hprod : len v * len w < r * r := by
    calc len v * len w ≤ len v * r := mul_le_mul_of_nonneg_left hw.le hv0
      _ < r * r := mul_lt_mul_of_pos_right hv hr_pos
  have hbound : |(E (a v) w : ℝ)| < 1 := by
    calc |(E (a v) w : ℝ)| ≤ len (a v) * len w := h.abs_E_le (a v) w
      _ ≤ (vr * len v) * len w := mul_le_mul_of_nonneg_right (h.len_a_le v) hw0
      _ = vr * (len v * len w) := by ring
      _ < vr * (r * r) := mul_lt_mul_of_pos_left hprod hvr
      _ = 1 := hrr
  have hint : |E (a v) w| < 1 := by exact_mod_cast hbound
  exact Int.abs_lt_one_iff.mp hint
end ShortVectorsOrthogonal
end GroundTheory.Heights₂.Heights.LowerBound
