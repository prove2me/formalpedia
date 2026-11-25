-- Prove2me | solution 1 for PI.WeylForKWork.blockReindex_mem_unitaryGroup_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:48:49.214205+00:00
-- url     : https://prove2.me/submissions/c953bd8c-c582-43f0-9e95-4e5c594d1453

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_Blocks
import Theorems.Thm_PI_WeylForKWork_star_blockReindex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WeylForKWork
open PI PI.UpqRep Matrix
variable {N : ℕ}
namespace PI.WeylForKWork
theorem _root_.solution (ε : Fin N → Bool) (M : Matrix (Fin (nPl ε) ⊕ Fin (nMi ε)) (Fin (nPl ε) ⊕ Fin (nMi ε)) ℂ) :
    blR ε M ∈ unitaryGroup (Fin N) ℂ ↔ M ∈ unitaryGroup _ ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.mem_unitaryGroup_iff, star_blockReindex, ← map_mul,
    ← map_one (blR ε), (blR ε).injective.eq_iff]
end PI.WeylForKWork
