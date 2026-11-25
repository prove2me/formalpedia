-- Prove2me | solution 1 for PI.WeylForKWork.blockReindex_mem_unitaryCentralizer_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:12:12.56634+00:00
-- url     : https://prove2.me/submissions/8834df2d-b3ca-4068-8194-1ab54cc3db09

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_Blocks
import Theorems.Thm_PI_WeylForKWork_signatureMatrix_eq_blockReindex
import Theorems.Thm_PI_WeylForKWork_blockReindex_mem_unitaryGroup_iff

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
    blR ε M ∈ Kset ε ↔ M ∈ unitaryGroup _ ℂ ∧ M * fromBlocks 1 0 0 (-1) = fromBlocks 1 0 0 (-1) * M := by
  show blR ε M ∈ unitaryGroup _ ℂ ∧ blR ε M * Jm ε = Jm ε * blR ε M ↔ _
  rw [blockReindex_mem_unitaryGroup_iff, signatureMatrix_eq_blockReindex, ← map_mul, ← map_mul, (blR ε).injective.eq_iff]
end PI.WeylForKWork
