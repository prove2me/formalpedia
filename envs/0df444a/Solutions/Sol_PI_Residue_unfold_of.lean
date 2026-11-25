-- Prove2me | solution 1 for PI.Residue.unfold_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:33:44.299157+00:00
-- url     : https://prove2.me/submissions/a0957b87-0387-4ce1-8cbd-5da45fded7f5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_BUnfold
import Theorems.Thm_PI_Residue_lattice_sum_le_shell_volume

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
open scoped nonZeroDivisors ENNReal Classical Pointwise
noncomputable section
open PI PI.Residue
variable {K : Type} [Field K] [NumberField K]
namespace PI.Residue
theorem _root_.solution (hUP : UnitPreserving) : Unfold :=
  fun _ _ _ J ρ _ => lattice_sum_le_shell_volume hUP J ρ
end PI.Residue
