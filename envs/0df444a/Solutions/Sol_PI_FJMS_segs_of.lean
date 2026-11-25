-- Prove2me | solution 1 for PI.FJMS.segs_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:44:25.364303+00:00
-- url     : https://prove2.me/submissions/db50112a-cbc5-4a24-aefb-00c5628bbff1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PosIffLtNP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_IsBlockHighestWeight
import Theorems.Thm_PI_FJMP_segJ_of
import Theorems.Thm_PI_FJM_leftDiagonalActionFormula
import Theorems.Thm_PI_FJM_leftOffDiagonalActionFormula
import Theorems.Thm_PI_FJM_rightDiagonalActionFormula
import Theorems.Thm_PI_FJM_rightOffDiagonalActionFormula
import Theorems.Thm_PI_WFJM_leftDiagonalActionFormula
import Theorems.Thm_PI_WFJM_leftOffDiagonalActionFormula
import Theorems.Thm_PI_WFJM_rightDiagonalActionFormula
import Theorems.Thm_PI_WFJM_rightOffDiagonalActionFormula


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
open PI PI.FJMS
open PI.FJM PI.FJMP
namespace PI.FJMS
theorem _root_.solution {p q r s : ℕ} {μ : Ix p q → ℚ} {μ' : Ix r s → ℚ} {P : Pol p q r s}
    (hM : MinHyp p q r s μ μ' P) : SegFacts p q r s μ μ' :=
  segJ_of leftDiagonalActionFormula rightDiagonalActionFormula leftOffDiagonalActionFormula rightOffDiagonalActionFormula p q r s μ μ' P hM
end PI.FJMS
