-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScGapBig.nat_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:42:21.397803+00:00
-- url     : https://prove2.me/submissions/e1827b84-accf-4152-b203-9a90744e8555

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScGapBig
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SpectralGapLarge_ScGapBigMain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScGapBig
open PI.ScGapBig
namespace PI.UnitaryGroupMassFormula.ScGapBig
theorem _root_.solution (n m t : ℕ) (hn : 1801 ≤ n) (hm : m ≤ n + 1) (ht : t ≤ n + 6) :
    2 * (n + m * t) ^ 3 + t + 3 < 16 * n ^ 19 := by
  have hmt : m * t ≤ (n + 1) * (n + 6) := Nat.mul_le_mul hm ht
  have hsq : 1801 * n ≤ n * n := Nat.mul_le_mul_right n hn
  have h1 : n + m * t ≤ 2 * n ^ 2 := by nlinarith
  have h2 : (n + m * t) ^ 3 ≤ (2 * n ^ 2) ^ 3 := Nat.pow_le_pow_left h1 3
  have h3 : (2 * n ^ 2) ^ 3 = 8 * n ^ 6 := by ring
  have h4 : 2 ≤ n ^ 13 :=
    le_trans (by norm_num) (Nat.pow_le_pow_left (show 2 ≤ n by omega) 13)
  have h5 : n ^ 19 = n ^ 6 * n ^ 13 := by ring
  have h6 : n ^ 6 * 2 ≤ n ^ 6 * n ^ 13 := Nat.mul_le_mul_left _ h4
  have h7 : n ≤ n ^ 6 := Nat.le_self_pow (by norm_num) n
  omega
end PI.UnitaryGroupMassFormula.ScGapBig
