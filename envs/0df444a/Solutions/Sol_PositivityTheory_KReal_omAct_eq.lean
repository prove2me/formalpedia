-- Prove2me | solution 1 for PositivityTheory.KReal.omAct_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:47.810242+00:00
-- url     : https://prove2.me/submissions/be54e264-c344-40d1-892f-65d992f92350

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_JointShape
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_FockAct1FockAct2Commute

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
open PositivityTheory PositivityTheory.KReal
variable {p q r s : ℕ}
namespace PositivityTheory.KReal
theorem _root_.solution (A : Matrix (Ln p q r s) (Ln p q r s) ℂ) :
    omAct p q r s A = quadT raiB lowB A + (∑ l, A l l * (1 / 2 : ℂ)) • 1 := by
  unfold omAct quadT omE
  simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, Matrix.entryLinearMap_apply,
    smul_add, Finset.sum_add_distrib, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, Finset.sum_smul, smul_smul]
end PositivityTheory.KReal
