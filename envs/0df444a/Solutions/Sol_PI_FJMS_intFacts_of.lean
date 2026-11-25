-- Prove2me | solution 1 for PI.FJMS.intFacts_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:45:35.303391+00:00
-- url     : https://prove2.me/submissions/4435d6eb-9458-4f54-b73f-9cc25120af39

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PosIffLtNP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_IsBlockHighestWeight
import Theorems.Thm_PI_FJMP_exists_mem_support
import Theorems.Thm_PI_FJMP_mem_leftHighestWeight_of_isMinimalJointVector
import Theorems.Thm_PI_FJMP_mem_rightHighestWeight_of_isMinimalJointVector
import Theorems.Thm_PI_FJMP_monomialLeftWeight_eq_weight_sub
import Theorems.Thm_PI_FJMP_monomialRightWeight_eq_weight_sub
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
namespace PI.FJMS
theorem _root_.solution {p q r s : ℕ} {μ : Ix p q → ℚ} {μ' : Ix r s → ℚ} {P : Pol p q r s}
    (hM : MinHyp p q r s μ μ' P) : IntFacts p q r s μ μ' := by
  obtain ⟨e0, he0⟩ := exists_mem_support hM.2.1
  refine ⟨fun a => ?_, fun c => ?_⟩
  · rw [← monomialLeftWeight_eq_weight_sub leftDiagonalActionFormula (mem_leftHighestWeight_of_isMinimalJointVector hM) e0 he0 a, Int.floor_intCast]
  · rw [← monomialRightWeight_eq_weight_sub rightDiagonalActionFormula (mem_rightHighestWeight_of_isMinimalJointVector hM) e0 he0 c, Int.floor_intCast]
end PI.FJMS
