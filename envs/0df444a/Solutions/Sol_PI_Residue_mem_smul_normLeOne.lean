-- Prove2me | solution 1 for PI.Residue.mem_smul_normLeOne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:44:10.795269+00:00
-- url     : https://prove2.me/submissions/131a061d-5ddf-437a-a447-3ea3e541e37e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_MemSmulNormLeOne
import Theorems.Thm_PI_Residue_cHalf_pos
import Theorems.Thm_PI_Residue_cHalf_pow

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
theorem _root_.solution (y : mixedSpace K) :
    y ∈ cHalf K • normLeOne K ↔ y ∈ fundamentalCone K ∧ mixedEmbedding.norm y ≤ 1 / 2 := by
  have hc := cHalf_pos K
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc.ne', mem_normLeOne,
    smul_mem_iff_mem (inv_ne_zero hc.ne'), mixedEmbedding.norm_smul, abs_of_pos (inv_pos.2 hc),
    inv_pow, cHalf_pow]
  refine and_congr_right fun _ => ?_
  constructor <;> intro h <;> linarith
end PI.Residue
