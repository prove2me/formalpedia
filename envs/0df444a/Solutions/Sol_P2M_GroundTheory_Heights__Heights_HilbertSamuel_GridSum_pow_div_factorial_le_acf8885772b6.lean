-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_GridSum_pow_div_factorial_le_acf8885772b6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:25:40.598818+00:00
-- url     : https://prove2.me/submissions/afac4e5b-3485-405e-a9d4-9da2ed06feb3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGridSum

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
open Finset Filter Asymptotics
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace GridSum
theorem _root_.solution (a i : ℕ) :
    (a : ℝ) ^ i / (i.factorial : ℝ) ≤ ((a + i).choose i : ℝ) := by
  rw [div_le_iff₀ (by positivity)]
  have h : a ^ i ≤ (a + i).choose i * i.factorial := by
    rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
    calc a ^ i ≤ (a + i + 1 - i) ^ i := Nat.pow_le_pow_left (by omega) i
      _ ≤ (a + i).descFactorial i := Nat.pow_sub_le_descFactorial _ _
  exact_mod_cast h
end GridSum
end GroundTheory.Heights₂.Heights.HilbertSamuel
