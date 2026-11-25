-- Prove2me | solution 1 for PI.TwoDivisibility.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:43:45.856014+00:00
-- url     : https://prove2.me/submissions/9e0b0e31-f492-46a9-868a-437f5c32a473

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerCoordinatesZero_IntCoordsZero
import Theorems.Thm_PI_TwoDivisibility_key

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.TwoDivisibility
namespace PI.TwoDivisibility
theorem _root_.solution : PI.KerLat.ExistsTwoTorsionOffKernels := by
  intro L d hd hθ
  set s : ℂ := ((Real.sqrt d : ℝ) : ℂ) with hsdef
  have hs : s * s = (d : ℂ) := by
    rw [hsdef, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg d)]
    simp
  have hd8 : (d : ℤ) = 8 * ((d / 8 : ℕ) : ℤ) + 7 := by omega
  set k : ℤ := ((d / 8 : ℕ) : ℤ) with hk
  have hk0 : 0 ≤ k := by positivity
  have hdC : (d : ℂ) = 8 * (k : ℂ) + 7 := by exact_mod_cast hd8
  have hq : ((1 + Complex.I * s) / 2) * ((1 + Complex.I * s) / 2) =
      ((1 + Complex.I * s) / 2) - ((2 * k + 2 : ℤ) : ℂ) := by
    push_cast
    linear_combination (-1 / 4 : ℂ) * hs + (-1 / 4 : ℂ) * hdC + (s * s / 4) * Complex.I_sq
  obtain ⟨t, h1, h2, h3⟩ := key L ((1 + Complex.I * s) / 2) (2 * k + 2) (by omega)
    ⟨k + 1, by ring⟩ hq hθ
  refine ⟨t, h1, h2, ?_⟩
  have : (1 - Complex.I * s) / 2 = 1 - (1 + Complex.I * s) / 2 := by ring
  rw [this]
  exact h3
end PI.TwoDivisibility
