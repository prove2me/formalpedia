-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ClassNumImQInv.minpoly_b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:43:36.469907+00:00
-- url     : https://prove2.me/submissions/4f2504d3-ca08-42f7-80b0-ed511818d867

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ClassNumImQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticInvariants_QuadPolyIrreducible
import Theorems.Thm_PI_UnitaryGroupMassFormula_ClassNumImQInv_quadPoly_monic
import Theorems.Thm_PI_UnitaryGroupMassFormula_ClassNumImQInv_aeval_quadPoly
import Theorems.Thm_PI_UnitaryGroupMassFormula_ClassNumImQInv_quadPoly_irreducible

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
theorem _root_.solution (hq : QuadData d K b) : minpoly ℚ b = quadPoly d := by
  exact (minpoly.eq_of_irreducible_of_monic (quadPoly_irreducible hq) (aeval_quadPoly hq)
    (quadPoly_monic d)).symm
end PI.UnitaryGroupMassFormula.ClassNumImQInv
