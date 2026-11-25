-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CntFormula.commonDen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:43:39.12655+00:00
-- url     : https://prove2.me/submissions/74b4a0d1-29d9-4b41-990f-2af5de763afe

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_IsIntIntCast
import Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_isInt_intCast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CntFormula
open NumberField
variable {K : Type} [Field K] [NumberField K]
namespace PI.UnitaryGroupMassFormula.CntFormula
theorem _root_.solution (s : Finset K) : ∃ d : ℕ, 0 < d ∧ ∀ x ∈ s, IsIntegral ℤ ((d : K) * x) := by
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ s
  refine ⟨y.natAbs ^ 2, pow_pos (Int.natAbs_pos.2 hy) 2, fun x hx => ?_⟩
  have e0 : ((y.natAbs ^ 2 : ℕ) : ℤ) = y ^ 2 := by rw [Nat.cast_pow, Int.natAbs_sq]
  have e1 : ((y.natAbs ^ 2 : ℕ) : K) = (y : K) ^ 2 := by rw [← Int.cast_natCast, e0, Int.cast_pow]
  rw [e1, pow_two, mul_assoc, ← zsmul_eq_mul x y]
  exact (isInt_intCast y).mul (h x hx)
end PI.UnitaryGroupMassFormula.CntFormula
