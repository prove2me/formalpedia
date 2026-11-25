-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnitDetRoot.det_mem_of_entries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:47:35.160867+00:00
-- url     : https://prove2.me/submissions/a5aec20b-29d5-4676-98d0-c66429274cdf

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_NsmulRelIdxMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_DetMemOfEntries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI
namespace PI.UnitaryGroupMassFormula.UnitDetRoot
theorem _root_.solution {m : Type} [Fintype m] [DecidableEq m] {S : IntermediateField ℚ ℂ}
    (U : Matrix m m ℂ) (h : ∀ i j, U i j ∈ S) : U.det ∈ S := by
  rw [Matrix.det_apply']
  exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => h _ _)
end PI.UnitaryGroupMassFormula.UnitDetRoot
