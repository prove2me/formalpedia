-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnipVal.Main.part2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:04:08.735566+00:00
-- url     : https://prove2.me/submissions/9de86f08-b06c-42b4-a8a9-7e8a8560fdef

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnipVal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentValuation_VwIntEqZero
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnipVal_Main_plc_prime
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnipVal_Main_part1
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnipVal_Main_pv_prime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnipVal PI.UnitaryGroupMassFormula.UnipVal.Main
open PI.UnipVal
variable {K : Type} [Field K] [NumberField K]
namespace PI.UnitaryGroupMassFormula.UnipVal.Main
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (g₁ g₂ a : ℕ) (h1 : g₁.Prime) (h2 : g₂.Prime)
    (h12 : g₁ ≠ g₂) :
    (vw w (((g₁ ^ a * g₂ ^ a : ℕ)) : K) : ℝ) =
      (ramw w : ℝ) * (if plc w = g₁ ∨ plc w = g₂ then (a : ℝ) else 0) := by
  have hp := plc_prime w
  haveI : Fact (plc w).Prime := ⟨hp⟩
  have ha1 : g₁ ^ a ≠ 0 := pow_ne_zero _ h1.ne_zero
  have ha2 : g₂ ^ a ≠ 0 := pow_ne_zero _ h2.ne_zero
  rw [part1 w _ (mul_ne_zero ha1 ha2), padicValNat.mul ha1 ha2, padicValNat.pow g₁ a,
    padicValNat.pow g₂ a, pv_prime _ _ hp h1, pv_prime _ _ hp h2]
  by_cases e1 : plc w = g₁
  · have e2 : plc w ≠ g₂ := fun e => h12 (e1.symm.trans e)
    rw [if_pos e1, if_neg e2, if_pos (Or.inl e1)]
    push_cast
    ring
  · by_cases e2 : plc w = g₂
    · rw [if_neg e1, if_pos e2, if_pos (Or.inr e2)]
      push_cast
      ring
    · rw [if_neg e1, if_neg e2, if_neg (not_or.mpr ⟨e1, e2⟩)]
      push_cast
      ring
end PI.UnitaryGroupMassFormula.UnipVal.Main
