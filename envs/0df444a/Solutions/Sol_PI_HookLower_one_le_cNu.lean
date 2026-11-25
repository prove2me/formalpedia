-- Prove2me | solution 1 for PI.HookLower.one_le_cNu
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:00:50.718493+00:00
-- url     : https://prove2.me/submissions/e9c5f65b-708c-4845-8ce1-524926a415e9

import Definitions.Def_Formalism_PeriodIntegrals_HookBound
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DiagonalMonomialFactorial
import Theorems.Thm_PI_HookLower_fockQ_hw_ge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open PI PI.HookLower
namespace PI.HookLower
theorem _root_.solution {N : ℕ} (ν : Fin N → ℕ) (hν : Antitone ν) : 1 ≤ PI.cNu ν := by
  have h := fockQ_hw_ge ν hν
  have hpos : (0 : ℝ) < ∏ l, ((ν l).factorial : ℝ) :=
    Finset.prod_pos fun l _ => by exact_mod_cast Nat.factorial_pos _
  have h' : (∏ l, ((ν l).factorial : ℝ)) ≤ ((fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) : ℚ) : ℝ) := by
    exact_mod_cast h
  unfold PI.cNu
  rw [one_le_div hpos]
  exact h'
end PI.HookLower
