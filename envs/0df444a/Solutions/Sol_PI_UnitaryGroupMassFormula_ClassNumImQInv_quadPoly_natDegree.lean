-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ClassNumImQInv.quadPoly_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:59.234619+00:00
-- url     : https://prove2.me/submissions/cf3c215f-31d8-4155-a9d2-f3e8b6567d31

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ClassNumImQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticInvariants_QuadPolyIrreducible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ClassNumImQInv
open PI.ClassNumImQ
variable {d : ℕ} {K : Type} [Field K] [NumberField K] {b : K}
namespace PI.UnitaryGroupMassFormula.ClassNumImQInv
theorem _root_.solution (d : ℕ) : (quadPoly d).natDegree = 2 := by
  unfold quadPoly
  exact Polynomial.natDegree_X_pow_add_C
end PI.UnitaryGroupMassFormula.ClassNumImQInv
