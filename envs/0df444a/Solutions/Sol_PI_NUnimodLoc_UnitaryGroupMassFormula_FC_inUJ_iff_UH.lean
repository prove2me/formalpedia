-- Prove2me | solution 1 for PI.NUnimodLoc.UnitaryGroupMassFormula.FC.inUJ_iff_UH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:00:12.644987+00:00
-- url     : https://prove2.me/submissions/1482a562-a04d-4deb-b51e-5be6fd5b9b76

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_FrameC
import Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_FC_gram_eq_Hpk
import Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_FC_pm_mul_qm
import Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_FC_conj_form

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
    inUJ ε g ↔ Qm k r ε e f wf z0 * g * Pm k r e f wf z0 ∈ UH (Hpk k r) := by
  have hPQ := pm_mul_qm hF
  have hQP' : (Qm k r ε e f wf z0)ᴴ * (Pm k r e f wf z0)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hPQ, Matrix.conjTranspose_one]
  have back : ∀ X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      (Qm k r ε e f wf z0)ᴴ * ((Pm k r e f wf z0)ᴴ * X * Pm k r e f wf z0) * Qm k r ε e f wf z0 = X := by
    intro X
    rw [show (Qm k r ε e f wf z0)ᴴ * ((Pm k r e f wf z0)ᴴ * X * Pm k r e f wf z0) * Qm k r ε e f wf z0
        = ((Qm k r ε e f wf z0)ᴴ * (Pm k r e f wf z0)ᴴ) * X * (Pm k r e f wf z0 * Qm k r ε e f wf z0) by
          simp only [Matrix.mul_assoc], hQP', hPQ, Matrix.one_mul, Matrix.mul_one]
  show gᴴ * Jm ε * g = Jm ε ↔ _ = _
  rw [conj_form hF, ← gram_eq_Hpk hF]
  constructor
  · intro h; rw [h]
  · intro h
    rw [← back (gᴴ * Jm ε * g), h, back]
end PI.NUnimodLoc.UnitaryGroupMassFormula.FC
