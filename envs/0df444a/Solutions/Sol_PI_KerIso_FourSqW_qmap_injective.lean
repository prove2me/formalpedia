-- Prove2me | solution 1 for PI.KerIso.FourSqW.qmap_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:55:25.018546+00:00
-- url     : https://prove2.me/submissions/74edbb50-1ab8-438b-bf62-ca2e7bc83c48

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_FourSqOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_QuatMatTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_QmapInjective
import Theorems.Thm_PI_KerIso_FourSqW_qmap_back

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
open PI PI.KerIso PI.KerIso.FourSqW
open PI.KerFourSqW
namespace PI.KerIso.FourSqW
theorem _root_.solution {K E : Type*} [Field K] [CharZero K] [Field E] [Algebra K E] {n : Type*}
    (b : Module.Basis n K E) (Q : n → Matrix (Fin 4) (Fin 4) ℚ) (q : n → ℚ) (hq : ∀ i, 0 < q i)
    (hQ : ∀ i, (Q i)ᵀ * Q i = q i • (1 : Matrix (Fin 4) (Fin 4) ℚ)) :
    Function.Injective (qmap b Q) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  funext a'
  rw [b.ext_elem_iff]
  intro i
  have h := qmap_back b Q q hQ x a' i
  simp only [hx, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h
  have hqi : (q i : K) ≠ 0 := by exact_mod_cast (hq i).ne'
  have h0 : b.repr (x a') i = 0 := by
    rcases mul_eq_zero.mp h.symm with h1 | h1
    · exact absurd h1 hqi
    · exact h1
  simp [h0]
end PI.KerIso.FourSqW
