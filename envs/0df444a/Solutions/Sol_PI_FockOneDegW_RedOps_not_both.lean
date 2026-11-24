-- Prove2me | solution 1 for PI.FockOneDegW.RedOps.not_both
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:26.891516+00:00
-- url     : https://prove2.me/submissions/4640e51e-836c-4b65-bdd1-1aaf816d9089

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_RedOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_ExistsMonomialWeight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_KernelHarmonic
import Theorems.Thm_FockRL_linePos_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FockOneDegW PI.FockOneDegW.RedOps
open PI.FockOneDegW
variable {p q r s : ℕ}
namespace PI.FockOneDegW.RedOps
theorem _root_.solution (c d : Ix r s) (hcd : ¬ sameBlock c d) (a : Ix p q)
    (h1 : linePos ((a, c) : Ln p q r s) = true) (h2 : linePos ((a, d) : Ln p q r s) = true) :
    False :=
  hcd ((FockRL.linePos_right a c d).1 (h1.trans h2.symm))
end PI.FockOneDegW.RedOps
