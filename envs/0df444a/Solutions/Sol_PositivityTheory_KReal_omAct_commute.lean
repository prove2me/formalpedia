-- Prove2me | solution 1 for PositivityTheory.KReal.omAct_commute
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:40:18.62241+00:00
-- url     : https://prove2.me/submissions/69868908-d68a-4805-9259-a1ac6f91cac0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_JointShape
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_FockAct1FockAct2Commute
import Theorems.Thm_PositivityTheory_KReal_quadT_commute
import Theorems.Thm_PositivityTheory_KReal_rai_rai
import Theorems.Thm_PositivityTheory_KReal_low_low
import Theorems.Thm_PositivityTheory_KReal_low_rai
import Theorems.Thm_PositivityTheory_KReal_omAct_eq

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
theorem _root_.solution (A B : Matrix (Ln p q r s) (Ln p q r s) ℂ) (h : A * B = B * A) :
    omAct p q r s A * omAct p q r s B = omAct p q r s B * omAct p q r s A := by
  have hc := quadT_commute raiB lowB rai_rai low_low low_rai A B h
  rw [omAct_eq, omAct_eq]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hc, smul_add, smul_smul]
  rw [mul_comm (∑ l, A l l * (1 / 2 : ℂ))]
  abel
end PositivityTheory.KReal
