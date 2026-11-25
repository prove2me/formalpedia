-- Prove2me | solution 1 for PI.Residue.prod_radius
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:13:08.449172+00:00
-- url     : https://prove2.me/submissions/c5c8ec60-9102-4678-98d0-9f746e8316b2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_LatticeCountGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_NormAtPlacePosOfNormPos

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
variable (K : Type) [Field K] [NumberField K]
variable {K}
namespace PI.Residue
theorem _root_.solution (ρ : ℝ) (y : mixedSpace K) :
    ∏ w : InfinitePlace K, (ρ / (2 * normAtPlace w y)) ^ mult w
      = (ρ / 2) ^ Module.finrank ℚ K / mixedEmbedding.norm y := by
  rw [mixedEmbedding.norm_apply, ← sum_mult_eq, ← Finset.prod_pow_eq_pow_sum,
    ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [← div_pow, div_div]
end PI.Residue
