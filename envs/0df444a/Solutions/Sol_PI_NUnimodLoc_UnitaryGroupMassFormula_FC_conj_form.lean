-- Prove2me | solution 1 for PI.NUnimodLoc.UnitaryGroupMassFormula.FC.conj_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:39:13.128814+00:00
-- url     : https://prove2.me/submissions/2377ad77-8ec7-40b6-aa5d-b8a0081ccdff

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_FrameC
import Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_FC_pm_mul_qm
import Theorems.Thm_Formalism_REAL_Jm_conjTranspose
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_Hpk_conjTranspose
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_Hpk_mul_self


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.NUnimodLoc PI.NUnimodLoc.UnitaryGroupMassFormula PI.NUnimodLoc.UnitaryGroupMassFormula.FC
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula.SW Formalism.REAL
variable {k r : ℕ}
variable {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
  {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z0 : Fin (2 * r + k + 1) → ℂ}
variable (hF : IsFrameJ ε e f wf z0)
include hF
namespace PI.NUnimodLoc.UnitaryGroupMassFormula.FC
theorem _root_.solution (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    (Qm k r ε e f wf z0 * g * Pm k r e f wf z0)ᴴ * Hpk k r * (Qm k r ε e f wf z0 * g * Pm k r e f wf z0) =
      (Pm k r e f wf z0)ᴴ * (gᴴ * Jm ε * g) * Pm k r e f wf z0 := by
  have hPQ := pm_mul_qm hF
  have hQH : (Qm k r ε e f wf z0)ᴴ = Jm ε * (Pm k r e f wf z0 * Hpk k r) := by
    unfold Qm
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Jm_conjTranspose,
      Hpk_conjTranspose]
  have hK : (Qm k r ε e f wf z0)ᴴ * Hpk k r * Qm k r ε e f wf z0 = Jm ε := by
    calc (Qm k r ε e f wf z0)ᴴ * Hpk k r * Qm k r ε e f wf z0
        = Jm ε * (Pm k r e f wf z0 * (Hpk k r * Hpk k r) * Qm k r ε e f wf z0) := by
          rw [hQH]; simp only [Matrix.mul_assoc]
      _ = Jm ε := by rw [Hpk_mul_self, Matrix.mul_one, hPQ, Matrix.mul_one]
  rw [← hK]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
end PI.NUnimodLoc.UnitaryGroupMassFormula.FC
