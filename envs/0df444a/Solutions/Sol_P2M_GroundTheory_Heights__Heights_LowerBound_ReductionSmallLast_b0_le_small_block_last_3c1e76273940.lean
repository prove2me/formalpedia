-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBound_ReductionSmallLast_b0_le_small_block_last_3c1e76273940
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:30:36.700142+00:00
-- url     : https://prove2.me/submissions/cbc85415-fa4a-4432-9429-7ee7885e5b9a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_PReductionSmallLast

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
namespace GroundTheory.Heights₂.Heights.LowerBound
namespace ReductionSmallLast
theorem _root_.solution {K1 Ca Cc A0 b0 hh sl rest vol J f j' n N j La : ℝ}
    (h : ReductionSmallLast.Hyp K1 Ca Cc A0 b0 hh sl rest vol J f j' n N j La) :
    b0 ≤ (1 / 2 + Ca + Cc) * La := by
  have hfj : 0 < f * j' := mul_pos h.f_pos h.j'_pos
  have hden : 0 < (n + 1) * vol * J := mul_pos (mul_pos h.n_succ_pos h.vol_pos) h.J_pos
  have hrest : rest / ((n + 1) * vol * J) ≤ Cc * (f * j') := by
    rw [div_le_iff₀ hden]
    have := (le_abs_self rest).trans h.rest_bound
    linarith
  have hhh : hh / ((n + 1) * J) ≤ f * j' / 2 * La :=
    h.hh_upper.trans (mul_le_mul_of_nonneg_left h.log_le_La (by positivity))
  have hCc : 0 ≤ Cc := by
    have h0 : 0 ≤ Cc * (f * j' * ((n + 1) * vol * J)) := by
      have := (abs_nonneg rest).trans h.rest_bound
      linarith
    exact nonneg_of_mul_nonneg_left h0 (mul_pos hfj hden)
  have hCcLa : Cc * (f * j') ≤ Cc * (f * j') * La :=
    le_mul_of_one_le_right (mul_nonneg hCc hfj.le) h.one_le_La
  have key : f * j' * b0 ≤ f * j' * ((1 / 2 + Ca + Cc) * La) := by
    rw [h.identity]
    nlinarith [h.sl_lower]
  exact le_of_mul_le_mul_left key hfj
end ReductionSmallLast
end GroundTheory.Heights₂.Heights.LowerBound
