-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ClassNumImQInt.half_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:38:23.925967+00:00
-- url     : https://prove2.me/submissions/32c824de-2500-4287-9d81-a31046d4355f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ClassNumImQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDifference_QuadraticDifferenceForm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ClassNumberIntegrality_HalfIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ClassNumImQInt
open NumberField Polynomial
namespace PI.UnitaryGroupMassFormula.ClassNumImQInt
theorem _root_.solution {K : Type} [Field K] [NumberField K] (d : ℕ) (b : K) (hd : d % 4 = 3)
    (hb : b ^ 2 = -(d : K)) : IsIntegral ℤ ((1 + b) / 2) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, d + 1 = 4 * k := ⟨(d + 1) / 4, by omega⟩
  have hk' : (d : K) + 1 = 4 * (k : K) := by exact_mod_cast hk
  refine ⟨X ^ 2 - X + C (k : ℤ), by monicity!, ?_⟩
  simp only [eval₂_add, eval₂_sub, eval₂_pow, eval₂_X, eval₂_natCast, map_natCast]
  linear_combination (1 / 4 : K) * hb - (1 / 4 : K) * hk'
end PI.UnitaryGroupMassFormula.ClassNumImQInt
