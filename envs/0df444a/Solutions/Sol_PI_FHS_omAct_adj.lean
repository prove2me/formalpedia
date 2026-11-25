-- Prove2me | solution 1 for PI.FHS.omAct_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:02:47.500145+00:00
-- url     : https://prove2.me/submissions/8062ae29-8df1-4f08-a8d3-6cdaa340a1e8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_FockInnerSelfReNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_ConjTransposeOneKronecker
import Theorems.Thm_PI_FHS_fockInner_sum_left
import Theorems.Thm_PI_FHS_fockInner_sum_right
import Theorems.Thm_PI_FHS_omE_adj
import Theorems.Thm_PI_FHS_omAct_apply
import Theorems.Thm_PI_FHS_fockInner_smul_left
import Theorems.Thm_PI_FHS_fockInner_smul_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix FockH1Action
open PI PI.FHS
variable {p q r s : ℕ}
namespace PI.FHS
theorem _root_.solution (M : Matrix (Ln p q r s) (Ln p q r s) ℂ) (hM : Mixed M) (P Q : Pol p q r s) :
    fockInner (omAct p q r s M P) Q = - fockInner P (omAct p q r s Mᴴ Q) := by
  rw [omAct_apply, omAct_apply]
  simp only [fockInner_sum_left, fockInner_sum_right, fockInner_smul_left,
    fockInner_smul_right, Matrix.conjTranspose_apply]
  conv_rhs => rw [Finset.sum_comm]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l' _ => ?_
  by_cases hz : M l l' = 0
  · simp [hz]
  · rw [omE_adj (hM l l' hz), mul_neg]
    rfl
end PI.FHS
