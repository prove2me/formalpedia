-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_div_le_padicValNat_factorial_9a940f801ab9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:05:28.144721+00:00
-- url     : https://prove2.me/submissions/e2545b9e-2b14-4347-8350-da12811cfcb1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PMertensUpper

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open Real
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution (N p : ℕ) (hp : p.Prime) :
    N / p ≤ padicValNat p N.factorial := by
  have := Fact.mk hp
  rcases lt_or_ge N p with h | h
  · rw [Nat.div_eq_of_lt h]; exact Nat.zero_le _
  · rw [padicValNat_factorial (b := Nat.log p N + 1) (Nat.lt_succ_self _)]
    have h1 : 1 ∈ Finset.Ico 1 (Nat.log p N + 1) := by
      have := Nat.log_pos hp.one_lt h
      simp only [Finset.mem_Ico]; omega
    have := Finset.single_le_sum (f := fun i => N / p ^ i) (fun _ _ => Nat.zero_le _) h1
    simpa using this
end GroundTheory.Heights₂.Heights.Model
