-- Prove2me | solution 1 for PI.OddDualWeyl.EvA.arith
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:57:30.938869+00:00
-- url     : https://prove2.me/submissions/245917e8-b0fb-43fe-9080-0dabc4c7a739

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_AevalMulHomog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_EvalDuality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl PI.OddDualWeyl.EvA
open Red
variable {K : Type} [Field K]
namespace PI.OddDualWeyl.EvA
theorem _root_.solution (x s : K) (hx : x ≠ 0) (hs : s * s = 1) (e e' : ℤ) (D M : ℕ)
    (h : e + e' + (D : ℤ) = (M : ℤ)) (y : K) :
    x ^ e * y = (x⁻¹ * s) ^ e' * (s ^ e' * (x⁻¹ ^ D * (x ^ M * y))) := by
  have hs' : s ^ e' * s ^ e' = 1 := by rw [← _root_.mul_zpow, hs, _root_.one_zpow]
  have key : x ^ e = x⁻¹ ^ e' * (x⁻¹ ^ D * x ^ M) := by
    have h1 : (x⁻¹ ^ D : K) = x ^ (-(D : ℤ)) := by rw [_root_.zpow_neg, _root_.zpow_natCast, _root_.inv_pow]
    have h2 : (x ^ M : K) = x ^ (M : ℤ) := (_root_.zpow_natCast x M).symm
    rw [h1, h2, _root_.inv_zpow', ← _root_.zpow_add₀ hx, ← _root_.zpow_add₀ hx]
    congr 1
    omega
  rw [key, _root_.mul_zpow]
  have h3 : (x⁻¹ ^ e' * s ^ e') * (s ^ e' * (x⁻¹ ^ D * (x ^ M * y))) =
      x⁻¹ ^ e' * (x⁻¹ ^ D * x ^ M) * y * (s ^ e' * s ^ e') := by ring
  rw [h3, hs', _root_.mul_one]
end PI.OddDualWeyl.EvA
