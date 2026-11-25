-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.mul_mem_S
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:22:40.718965+00:00
-- url     : https://prove2.me/submissions/4fa8b173-ac19-4287-aec5-a691f2a82692

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnipotentRadicalContracting
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_IsClosedS
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_inv_inv_UH
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_inv_mem_UW
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_mul_inv_UH
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_mul_mem_UW
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
theorem _root_.solution {a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ Sset k r z) (hb : b ∈ Sset k r z) : a * b ∈ Sset k r z := by
  obtain ⟨h1, hh1, n1, hn1, rfl⟩ := ha
  obtain ⟨h2, hh2, n2, hn2, rfl⟩ := hb
  have hi2 := inv_mem_UW hh2
  have hc : h2⁻¹ * n1 * h2 ∈ Nset k r := by
    have := uw_conj_N hi2 hn1; rwa [inv_inv_UH hh2.1] at this
  refine ⟨h1 * h2, mul_mem_UW hh1 hh2, h2⁻¹ * n1 * h2 * n2, (nilpotent_subgroup k r).2.1 _ hc _ hn2, ?_⟩
  calc h1 * n1 * (h2 * n2) = h1 * (h2 * h2⁻¹) * n1 * h2 * n2 := by
        rw [mul_inv_UH hh2.1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = h1 * h2 * (h2⁻¹ * n1 * h2 * n2) := by simp only [Matrix.mul_assoc]
end PI.QuotSetU.UnitaryGroupMassFormula.SW
