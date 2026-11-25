-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.dS_conj_S
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:34:15.740416+00:00
-- url     : https://prove2.me/submissions/3be6f4d7-3e09-4c68-97df-e71c0876594e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MulVecBvecApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnipotentRadicalContracting
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_dS_mul_dS_inv
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_dS_conj_UW
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_dS_conj_N

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
theorem _root_.solution {s : ℝ} (hs : s ≠ 0) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ Sset k r z) : dS k r s * g * dS k r s⁻¹ ∈ Sset k r z := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hg
  have h1 : dS k r s⁻¹ * dS k r s = 1 := by
    have := dS_mul_dS_inv (k := k) (r := r) (inv_ne_zero hs)
    rwa [inv_inv] at this
  have e : dS k r s * (h * m) * dS k r s⁻¹ =
      (dS k r s * h * dS k r s⁻¹) * (dS k r s * m * dS k r s⁻¹) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (dS k r s⁻¹) (dS k r s), h1, Matrix.one_mul]
  exact ⟨h, hh, _, dS_conj_N hs hm, by rw [e, dS_conj_UW hs hh]⟩
end PI.QuotSetU.UnitaryGroupMassFormula.SW
