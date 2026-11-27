-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ClassNumImQInv.finrank_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:18:27.219896+00:00
-- url     : https://prove2.me/submissions/ab3ef3e7-3d69-4c71-9713-25c36090c444

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ClassNumImQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticInvariants_QuadPolyIrreducible
import Theorems.Thm_PI_UnitaryGroupMassFormula_ClassNumImQInv_quadPoly_natDegree
import Theorems.Thm_PI_UnitaryGroupMassFormula_ClassNumImQInv_minpoly_b

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
theorem _root_.solution (hq : QuadData d K b) : Module.finrank ℚ K = 2 := by
  have hI : IsIntegral ℚ b := IsIntegral.of_finite ℚ b
  rw [← IntermediateField.finrank_top', ← hq.2.2.2.2, IntermediateField.adjoin.finrank hI, minpoly_b hq,
    quadPoly_natDegree]
end PI.UnitaryGroupMassFormula.ClassNumImQInv
