-- Prove2me | solution 1 for PI.OddDualWeyl.isUnit_revInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:11:31.47282+00:00
-- url     : https://prove2.me/submissions/48a42271-7e22-4a29-acda-d4f9f278761b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_RevColOneTranspose
import Theorems.Thm_PI_OddDualWeyl_isUnit_invT
import Theorems.Thm_PI_OddDualWeyl_revCol_eq
import Theorems.Thm_PI_OddDualWeyl_revCol_one_mul_self

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
    IsUnit (revCol (z⁻¹)ᵀ).det := by
  have hP : IsUnit (revCol (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K)).det := by
    have h : (revCol (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K)).det *
        (revCol (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K)).det = 1 := by
      rw [← det_mul, revCol_one_mul_self, det_one]
    exact ⟨⟨_, _, h, h⟩, rfl⟩
  rw [revCol_eq, det_mul]
  exact (isUnit_invT hz).mul hP
end PI.OddDualWeyl
