-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.dS_mem_UH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:20:58.816899+00:00
-- url     : https://prove2.me/submissions/827852dc-ccfd-4aba-b2ad-962a600fdc60

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MulVecBvecApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnipotentRadicalContracting
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_fexp_piI
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_Hpk_apply


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
theorem _root_.solution {s : ℝ} (hs : s ≠ 0) : dS k r s ∈ UH (Hpk k r) := by
  show (dS k r s)ᴴ * Hpk k r * dS k r s = Hpk k r
  ext i j
  rw [dS, diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul, Hpk_apply]
  split_ifs with h
  · subst h
    have hs' : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
    rw [fexp_piI, Pi.star_apply, star_zpow₀, Complex.star_def, Complex.conj_ofReal, _root_.zpow_neg]
    field_simp
  · simp
end PI.QuotSetU.UnitaryGroupMassFormula.SW
