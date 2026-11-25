-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.mem_S_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:12:22.785798+00:00
-- url     : https://prove2.me/submissions/c7652935-839b-4f6c-89ca-2c919dbcd40c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnipotentRadicalContracting
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_IsClosedS
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_inv_eq_UH
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_inv_mul_UH
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_mul_inv_UH


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
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW
open PI PI.QuotSetU
variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
namespace PI.QuotSetU.UnitaryGroupMassFormula.SW
theorem _root_.solution (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    g ∈ Sset k r z ↔ ∃ h ∈ UWset k r z, Hpk k r * hᴴ * Hpk k r * g ∈ Nset k r := by
  constructor
  · rintro ⟨h, hh, n, hn, rfl⟩
    refine ⟨h, hh, ?_⟩
    rw [← Matrix.mul_assoc, inv_mul_UH hh.1, Matrix.one_mul]; exact hn
  · rintro ⟨h, hh, hn⟩
    refine ⟨h, hh, _, hn, ?_⟩
    rw [← inv_eq_UH hh.1, ← Matrix.mul_assoc, mul_inv_UH hh.1, Matrix.one_mul]
end PI.QuotSetU.UnitaryGroupMassFormula.SW
