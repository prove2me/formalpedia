-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.muM_common
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:38:29.226663+00:00
-- url     : https://prove2.me/submissions/55363f59-545e-4174-85d0-5709a4c31b04

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_MuMEvalPowEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM Polynomial
variable (l : ℕ) [Fact l.Prime]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (S : Finset (muM l)) :
    ∃ n : ℕ, 0 < n ∧ ¬ l ∣ n ∧ ∀ a ∈ S, (a : ℂ_[l]) ^ n = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, fun h => (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.1 h), by simp⟩
  | insert a S _ ih =>
    obtain ⟨n, hn, hln, hS⟩ := ih
    obtain ⟨m, hm, hlm, ha⟩ := a.2
    refine ⟨n * m, Nat.mul_pos hn hm, fun h => ?_, ?_⟩
    · rcases ((Fact.out : l.Prime).dvd_mul).1 h with h | h
      · exact hln h
      · exact hlm h
    · intro b hb
      rcases Finset.mem_insert.1 hb with rfl | hb
      · rw [mul_comm, pow_mul, ha, one_pow]
      · rw [pow_mul, hS b hb, one_pow]
end ReciprocityTheory.ChartRestriction.L1
