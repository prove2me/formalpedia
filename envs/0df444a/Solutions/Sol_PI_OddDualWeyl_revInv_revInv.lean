-- Prove2me | solution 1 for PI.OddDualWeyl.revInv_revInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:05:35.972879+00:00
-- url     : https://prove2.me/submissions/0a778f9c-0701-4ca5-8e5c-17f0d31a8394

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_RevColOneTranspose
import Theorems.Thm_PI_OddDualWeyl_invT_invT
import Theorems.Thm_PI_OddDualWeyl_revCol_eq
import Theorems.Thm_PI_OddDualWeyl_revCol_one_mul_self
import Theorems.Thm_PI_OddDualWeyl_revCol_one_transpose

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
open PI PI.OddDualWeyl
variable {K : Type} [Field K]
namespace PI.OddDualWeyl
theorem _root_.solution {m : ℕ} {z : Matrix (Fin (m + 1)) (Fin (m + 1)) K} (hz : IsUnit z.det) :
    revCol ((revCol (z⁻¹)ᵀ)⁻¹)ᵀ = z := by
  have hP : revCol (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K) * revCol 1 = 1 :=
    revCol_one_mul_self
  have hPinv : (revCol (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K))⁻¹ = revCol 1 :=
    inv_eq_left_inv hP
  rw [revCol_eq ((z⁻¹)ᵀ), Matrix.mul_inv_rev, hPinv, transpose_mul, invT_invT hz,
    revCol_one_transpose, revCol_eq (z * revCol 1), mul_assoc, hP, mul_one]
end PI.OddDualWeyl
