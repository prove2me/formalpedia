-- Prove2me | solution 1 for PI.Residue.tsum_eq_zero_add_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:13:49.127983+00:00
-- url     : https://prove2.me/submissions/9d395e84-4301-4162-ae1d-d4e8d1b31121

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_BUnfold

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
theorem _root_.solution {α : Type*} [Zero α] (f : α → ℝ≥0∞) :
    ∑' x, f x = f 0 + ∑' x : {x : α // x ≠ 0}, f x := by
  rw [ENNReal.tsum_eq_add_tsum_ite 0]
  change _ = f 0 + ∑' x : ↑{x : α | x ≠ 0}, f x
  rw [tsum_subtype {x : α | x ≠ 0} f]
  congr 1
  refine tsum_congr fun x => ?_
  by_cases h : x = 0 <;> simp [h]
end PI.Residue
