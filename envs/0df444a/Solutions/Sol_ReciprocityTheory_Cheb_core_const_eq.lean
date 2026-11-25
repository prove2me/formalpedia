-- Prove2me | solution 1 for ReciprocityTheory.Cheb.core_const_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:42:27.054544+00:00
-- url     : https://prove2.me/submissions/0028dab9-0700-4ac6-89e7-68f3b4b4863a

import Definitions.Def_ReciprocityTheory_Chebotarev_AbsLogSubLogLeOfHalf
import Definitions.Def_ReciprocityTheory_Chebotarev_RpowNegFinrankSubOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
theorem _root_.solution {A B c d t : ℝ} (n : ℕ) (hc : 0 < c) (ht : 0 < t) :
    (A * (4 * (2 * B / (c * t))) + 2 * (d * (2 * B / (c * t)))) * (((c * t) / 2) ^ n)⁻¹ =
      ((8 * A * B + 4 * d * B) / c * (2 / c) ^ n) * (t ^ (n + 1))⁻¹ := by
  rw [div_pow, inv_div, div_pow, mul_pow, pow_succ]
  field_simp
  ring
end ReciprocityTheory.Cheb
