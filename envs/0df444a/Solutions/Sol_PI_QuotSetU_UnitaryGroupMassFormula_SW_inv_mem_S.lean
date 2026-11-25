-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.inv_mem_S
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:22:35.265155+00:00
-- url     : https://prove2.me/submissions/67341a01-d566-453c-bc05-4ff704891001

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnipotentRadicalContracting
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_IsClosedS
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_S_sub_UH
import Theorems.Thm_P2M_PI_QuotSetU_UnitaryGroupMassFormula_SW_inv_mul_UH__f897c67e29e4
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_inv_mem_UW
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_mul_inv_UH
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_nilpotent_subgroup
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_uw_conj_N


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
theorem _root_.solution {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ Sset k r z) : a⁻¹ ∈ Sset k r z ∧ a * a⁻¹ = 1 := by
  refine ⟨?_, mul_inv_UH (S_sub_UH ha)⟩
  obtain ⟨h, hh, n, hn, rfl⟩ := ha
  have hi := inv_mem_UW hh
  have hni : n⁻¹ ∈ Nset k r := (nilpotent_subgroup k r).2.2 _ hn
  refine ⟨h⁻¹, hi, h * n⁻¹ * h⁻¹, uw_conj_N hh hni, ?_⟩
  rw [Matrix.mul_inv_rev]
  calc n⁻¹ * h⁻¹ = (h⁻¹ * h) * n⁻¹ * h⁻¹ := by rw [inv_mul_UH' hh.1, Matrix.one_mul]
    _ = h⁻¹ * (h * n⁻¹ * h⁻¹) := by simp only [Matrix.mul_assoc]
end PI.QuotSetU.UnitaryGroupMassFormula.SW
