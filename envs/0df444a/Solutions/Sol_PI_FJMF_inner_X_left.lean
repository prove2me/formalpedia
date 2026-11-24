-- Prove2me | solution 1 for PI.FJMF.inner_X_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:27.327077+00:00
-- url     : https://prove2.me/submissions/3250c721-20b7-4f4d-b6f0-23b8ab744f31

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_EqZeroOfFockInnerSelfRe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_BlockDegreeAntitone
import Theorems.Thm_PI_FJMF_inner_conj
import Theorems.Thm_FockRaiseLowInner_fockInner_mul_X


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial FockH1Action
open PI PI.FJMF
variable {σ : Type}
namespace PI.FJMF
theorem _root_.solution (l : σ) (P Q : MvPolynomial σ ℂ) :
    fockInner (X l * P) Q = fockInner P (pderiv l Q) := by
  rw [inner_conj Q (X l * P), FockRaiseLowInner.fockInner_mul_X, inner_conj P (pderiv l Q), Complex.conj_conj]
end PI.FJMF
