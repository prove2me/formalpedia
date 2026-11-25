-- Prove2me | solution 1 for PI.EF.card_le_sum_mult
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:50:15.995287+00:00
-- url     : https://prove2.me/submissions/cb2dd610-c6c2-467a-8329-517b4d9f2d20

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeight
import Theorems.Thm_PI_EF_one_le_mult
import Theorems.Thm_PI_EF_ne_one_of_re_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open DirichletCharacter
namespace PI.EF
theorem _root_.solution {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (B : Finset ℂ)
    (hB : ∀ ρ ∈ B, ρ.re < 1 ∧ LFunction χ ρ = 0) :
    (B.card : ℝ) ≤ ∑ ρ ∈ B, (mult χ ρ : ℝ) := by
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro ρ hρ
  obtain ⟨h1, h0⟩ := hB ρ hρ
  exact_mod_cast one_le_mult χ (ne_one_of_re_lt h1) h0
end PI.EF
