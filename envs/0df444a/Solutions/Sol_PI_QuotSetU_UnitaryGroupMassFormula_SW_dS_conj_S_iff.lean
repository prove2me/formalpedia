-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.dS_conj_S_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:39:18.049109+00:00
-- url     : https://prove2.me/submissions/0d254185-795a-496c-8316-c861926972b4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MulVecBvecApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnipotentRadicalContracting
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_dS_mul_dS_inv
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_dS_conj_S
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_dS_inv_eq

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
theorem _root_.solution {s : ℝ} (hs : s ≠ 0) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    dS k r s * g * (dS k r s)⁻¹ ∈ Sset k r z ↔ g ∈ Sset k r z := by
  rw [dS_inv_eq hs]
  have h1 : dS k r s⁻¹ * dS k r s = 1 := by
    have := dS_mul_dS_inv (k := k) (r := r) (inv_ne_zero hs)
    rwa [inv_inv] at this
  constructor
  · intro hg
    have h2 := dS_conj_S (inv_ne_zero hs) hg
    rw [inv_inv] at h2
    have e : dS k r s⁻¹ * (dS k r s * g * dS k r s⁻¹) * dS k r s = g := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h1,
        Matrix.mul_one]
    rwa [e] at h2
  · exact dS_conj_S hs
end PI.QuotSetU.UnitaryGroupMassFormula.SW
