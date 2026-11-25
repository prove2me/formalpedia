-- Prove2me | solution 1 for PI.Residue.shell_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:13:23.33446+00:00
-- url     : https://prove2.me/submissions/d96c84dc-0fc5-441f-bd99-6d0b13268580

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_MemSmulNormLeOne
import Theorems.Thm_PI_Residue_mem_smul_normLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.InfinitePlace NumberField.Units MeasureTheory
open scoped ENNReal Classical Pointwise
noncomputable section
open PI PI.Residue
variable (K : Type) [Field K] [NumberField K]
namespace PI.Residue
theorem _root_.solution : shell K = normLeOne K \ (cHalf K • normLeOne K) := by
  ext y
  rw [Set.mem_sdiff, mem_smul_normLeOne, mem_normLeOne]
  simp only [shell, Set.mem_ofPred_eq, not_and, not_le]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h3⟩, fun _ => h2⟩
  · rintro ⟨⟨h1, h3⟩, h2⟩; exact ⟨h1, h2 h1, h3⟩
end PI.Residue
