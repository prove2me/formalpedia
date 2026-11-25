-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.dS_conj_N
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:26:52.227855+00:00
-- url     : https://prove2.me/submissions/fcd988d6-e79a-48d9-a91d-97304660f986

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MulVecBvecApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnipotentRadicalContracting
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_dS_mem_UH
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_dS_conj_fix
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_mem_Nset_iff
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_mul_mem_UH


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
theorem _root_.solution {s : ℝ} (hs : s ≠ 0) {n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hn : n ∈ Nset k r) : dS k r s * n * dS k r s⁻¹ ∈ Nset k r := by
  rw [mem_Nset_iff] at hn ⊢
  exact ⟨mul_mem_UH (mul_mem_UH (dS_mem_UH hs) hn.1) (dS_mem_UH (inv_ne_zero hs)),
    fun i j hj hi => dS_conj_fix hs i j (hn.2 i j hj hi)⟩
end PI.QuotSetU.UnitaryGroupMassFormula.SW
