-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.dS_conj_UW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:18:29.741346+00:00
-- url     : https://prove2.me/submissions/a9dce6b1-fb8e-409d-ab5c-69391236fad3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MulVecBvecApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnipotentRadicalContracting
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_fexp_inW
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_dS_conj_apply
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_dS_conj_fix
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_uw_block


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
theorem _root_.solution {s : ℝ} (hs : s ≠ 0) {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) : dS k r s * h * dS k r s⁻¹ = h := by
  ext i j
  by_cases hij : inW k r i ∧ inW k r j
  · rw [dS_conj_apply, fexp_inW hij.1, fexp_inW hij.2, zpow_zero, zpow_zero, one_mul, mul_one]
  · rw [dS_conj_fix hs i j (uw_block hh i j hij), uw_block hh i j hij]
end PI.QuotSetU.UnitaryGroupMassFormula.SW
