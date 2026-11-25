-- Prove2me | solution 1 for PI.OddDualWeyl.Red.adj_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:59:10.824905+00:00
-- url     : https://prove2.me/submissions/360e50f7-5626-4ca4-bedc-cf294467ecb3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_AevalMulHomog
import Theorems.Thm_PI_OddDualWeyl_Red_det_inv_eq

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
open PI PI.OddDualWeyl PI.OddDualWeyl.Red
variable {R : Type*} [CommRing R] {k : ℕ}
variable {K : Type*} [Field K] {k : ℕ}
namespace PI.OddDualWeyl.Red
theorem _root_.solution (g : Matrix (Fin k) (Fin k) K) (hd : g.det ≠ 0) : (g⁻¹).adjugate = (g.det)⁻¹ • g := by
  have hu : IsUnit g.det := isUnit_iff_ne_zero.mpr hd
  calc (g⁻¹).adjugate = g * (g⁻¹ * (g⁻¹).adjugate) := by
        rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv g hu, Matrix.one_mul]
    _ = (g.det)⁻¹ • g := by
        rw [Matrix.mul_adjugate, det_inv_eq, Matrix.mul_smul, Matrix.mul_one]
end PI.OddDualWeyl.Red
