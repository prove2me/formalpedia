-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_GridSum_choose_le_pow_div_factorial_e7e62f8ad023
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:25:39.983804+00:00
-- url     : https://prove2.me/submissions/edb8d778-c0b5-4c81-87b8-e3509f4644c7

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
    (a.choose i : ℝ) ≤ (a : ℝ) ^ i / (i.factorial : ℝ) := by
  rw [le_div_iff₀ (by positivity)]
  have h : a.choose i * i.factorial ≤ a ^ i := by
    rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow a i
  exact_mod_cast h
end GridSum
end GroundTheory.Heights₂.Heights.HilbertSamuel
