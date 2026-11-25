-- Prove2me | solution 1 for PI.WeylForKWork.plusBlock_mem_unitaryCentralizer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:18:47.05412+00:00
-- url     : https://prove2.me/submissions/bc9962f5-e0c5-4836-9012-5dfce376f3f9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_Blocks
import Theorems.Thm_PI_WeylForKWork_plusBlock_eq_blockReindex
import Theorems.Thm_PI_WeylForKWork_blockReindex_mem_unitaryCentralizer_iff
import Theorems.Thm_PI_WeylForKWork_mem_unitaryCentralizer_allPos_iff
import Theorems.Thm_PI_WeylForKWork_fromBlocks_diagonal_mem_unitaryGroup_iff
import Theorems.Thm_PI_WeylForKWork_fromBlocks_diagonal_mul_signature_comm

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
theorem _root_.solution (ε : Fin N → Bool) (h : Matrix (Fin (nPl ε)) (Fin (nPl ε)) ℂ)
    (hh : h ∈ Kset (allPos (nPl ε))) : iPl ε h ∈ Kset ε := by
  rw [mem_unitaryCentralizer_allPos_iff] at hh
  rw [plusBlock_eq_blockReindex, blockReindex_mem_unitaryCentralizer_iff]
  exact ⟨(fromBlocks_diagonal_mem_unitaryGroup_iff _ _).2 ⟨hh, one_mem _⟩, fromBlocks_diagonal_mul_signature_comm _ _⟩
end PI.WeylForKWork
