-- Prove2me | solution 1 for PI.FJMX.vecHW2_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:34:04.123626+00:00
-- url     : https://prove2.me/submissions/93f1eaa8-b72d-4877-a014-93812ebd152a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistWt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistPad
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_IsDiagonalBlockIndexRightOfPositiveRoot
import Theorems.Thm_PI_FJMX_mem_wtSub2
import Theorems.Thm_PI_FJMX_posC_ne
import Theorems.Thm_PI_FJMX_isDiagonalBlockIndex_right_of_positiveRoot
import Theorems.Thm_PI_FJMX_wtVec2
import Theorems.Thm_PI_FJMX_rightRootOperator_eq_derivation
import Theorems.Thm_PI_FJMX_vecRaise2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial FockH1Action PI.FJM
noncomputable section
open PI PI.FJMX
variable {p q r s : ℕ}
namespace PI.FJMX
theorem _root_.solution (hW : FormWt2) (hR : FormRaise2) : VecHW2 := by
  intro p q r s a b c d hd
  refine Submodule.mem_inf.2 ⟨mem_wtSub2 hW _ _ (wtVec2 a b c d hd), ?_⟩
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  intro x y hxy
  rw [hR p q r s x y (posC_ne x y hxy), rightRootOperator_eq_derivation x y (posC_ne x y hxy) (isDiagonalBlockIndex_right_of_positiveRoot x y hxy)]
  exact vecRaise2 a b c d x y hxy
end PI.FJMX
