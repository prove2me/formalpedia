-- Prove2me | solution 1 for PI.WeylForKWork.prod_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:48:47.153925+00:00
-- url     : https://prove2.me/submissions/a28b8b32-3436-4816-aa9b-44670730deeb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_Formula

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
open PI PI.UpqRep Matrix Finset
variable {N : ℕ}
namespace PI.WeylForKWork
theorem _root_.solution {M : Type*} [CommMonoid M] (ε : Fin N → Bool) (f : Fin N → M) :
    ∏ a, f a = (∏ i, f (ePl ε i)) * ∏ j, f (eMi ε j) := by
  rw [← Equiv.prod_comp (blk ε), Fintype.prod_sum_type]
  rfl
end PI.WeylForKWork
