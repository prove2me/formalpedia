-- Prove2me | solution 1 for XorParallelRepetition.Exponential.parallel_repetition_exponential
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:40:25.195731+00:00
-- url     : https://prove2.me/submissions/c5375808-23fb-40ce-925b-ef396d7f0024

import Mathlib
import Definitions.Def_XorParallelRepetition_Exponential_XorGames
import Definitions.Def_XorParallelRepetition_Exponential_BLR
import Theorems.Thm_XorParallelRepetition_Exponential_blr_exponential_decay
import Theorems.Thm_XorParallelRepetition_Exponential_repeated_value_le_blr
universe u

section
set_option autoImplicit false

namespace XorParallelRepetition.Exponential


theorem chk_parallel_repetition_exponential {p : ℕ} [Fact p.Prime] {ι : Type} [Fintype ι]
    (Ψ : XorGame.{u} p ι) (hval : Ψ.val < 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ n : ℕ, Ψ.repVal n ≤ (1 - ε) ^ n := by
  classical
  obtain ⟨ε, hε, h⟩ := blr_exponential_decay Ψ hval
  exact ⟨ε, hε, fun n => (repeated_value_le_blr Ψ n).trans (h n)⟩

end XorParallelRepetition.Exponential
end

theorem solution : type_of% @XorParallelRepetition.Exponential.chk_parallel_repetition_exponential := @XorParallelRepetition.Exponential.chk_parallel_repetition_exponential
