-- Prove2me | solution 1 for PI.FJMS.pure_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:44:46.183372+00:00
-- url     : https://prove2.me/submissions/8483d50a-fb44-4d1f-a092-add630d19ea3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MemLeftHighestWeightOfIsMinimalJointVector
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Definitions.Def_Lemmata_B1959r_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PosIffLtNP
import Theorems.Thm_PI_FJMP_pureJ_of
import Theorems.Thm_PI_FJM_leftDiagonalActionFormula
import Theorems.Thm_PI_FJM_rightDiagonalActionFormula
import Theorems.Thm_PI_WFJM_leftDiagonalActionFormula
import Theorems.Thm_PI_WFJM_rightDiagonalActionFormula


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
variable {p q r s : ℕ} {μ : Ix p q → ℚ} {μ' : Ix r s → ℚ} {P : Pol p q r s}
namespace PI.FJMS
theorem _root_.solution (hM : MinHyp p q r s μ μ' P) {e : Ln p q r s →₀ ℕ} (he : e ∈ P.support) {l : Ln p q r s}
    (hl : e l ≠ 0) : nu1 p q r s μ l.1 ≠ 0 ∧ nu2 p q r s μ' l.2 ≠ 0 ∧
      (linePos l = true ↔ 0 < nu1 p q r s μ l.1) ∧ (linePos l = true ↔ 0 < nu2 p q r s μ' l.2) :=
  pureJ_of leftDiagonalActionFormula rightDiagonalActionFormula p q r s μ μ' P hM e he l hl
end PI.FJMS
