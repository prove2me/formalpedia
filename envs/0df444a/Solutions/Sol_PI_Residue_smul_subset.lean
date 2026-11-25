-- Prove2me | solution 1 for PI.Residue.smul_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:13:32.745185+00:00
-- url     : https://prove2.me/submissions/15e13d77-07d4-4ca5-9e29-6285a76979de

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
theorem _root_.solution : cHalf K • normLeOne K ⊆ normLeOne K := by
  intro y hy
  rw [mem_smul_normLeOne] at hy
  exact mem_normLeOne.2 ⟨hy.1, hy.2.trans (by norm_num)⟩
end PI.Residue
