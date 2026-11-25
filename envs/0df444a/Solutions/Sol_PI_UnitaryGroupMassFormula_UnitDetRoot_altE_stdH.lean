-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnitDetRoot.altE_stdH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:57:17.481257+00:00
-- url     : https://prove2.me/submissions/e4916909-9aea-4678-8ea5-d59017c4a0af

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobalLUnit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_NsmulRelIdxMem
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_stdH_apply

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
theorem _root_.solution {m : Type} [Fintype m] [DecidableEq m] (L : PeriodPair) (x y : m → ℂ) :
    UnitDetRootDefs.altE (UnitDetRootDefs.stdH L m) x y = ∑ i, (x i * conj (y i)).im / UnitDetRootDefs.area L := by
  rw [UnitDetRootDefs.altE, stdH_apply, Complex.im_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm (x i), mul_assoc, ← Complex.ofReal_inv, Complex.im_ofReal_mul]
  field_simp
end PI.UnitaryGroupMassFormula.UnitDetRoot
