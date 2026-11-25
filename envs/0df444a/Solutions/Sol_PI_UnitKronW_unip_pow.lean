-- Prove2me | solution 1 for PI.UnitKronW.unip_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:38:42.952498+00:00
-- url     : https://prove2.me/submissions/880fe73d-77ae-40c9-bc8a-8508f7067f4f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitKronecker_PosDefFormNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitKronecker_EqZeroOfMulVec
import Theorems.Thm_PI_UnitKronW_eq_zero_of_mulVec
import Theorems.Thm_PI_UnitKronW_unip_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitKronW
open Matrix Polynomial ComplexOrder
namespace PI.UnitKronW
theorem _root_.solution {k : ℕ} {H W : Matrix (Fin k) (Fin k) ℂ} (hH : H.PosDef) (hW : Wᴴ * H * W = H) :
    ∀ j : ℕ, (W - 1) ^ (j + 1) = 0 → W - 1 = 0 := by
  intro j
  induction j with
  | zero => intro h; simpa using h
  | succ j ih =>
    intro h
    apply ih
    apply eq_zero_of_mulVec
    intro x
    have e : (W - 1) ^ (j + 1 + 1) *ᵥ x = (W - 1) *ᵥ ((W - 1) *ᵥ ((W - 1) ^ j *ᵥ x)) := by
      rw [pow_succ', pow_succ', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have h2 : (W - 1) *ᵥ ((W - 1) *ᵥ ((W - 1) ^ j *ᵥ x)) = 0 := by
      rw [← e, h, Matrix.zero_mulVec]
    have h3 := unip_step hH hW _ h2
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    exact h3
end PI.UnitKronW
