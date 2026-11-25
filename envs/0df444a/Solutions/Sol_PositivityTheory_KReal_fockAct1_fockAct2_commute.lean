-- Prove2me | solution 1 for PositivityTheory.KReal.fockAct1_fockAct2_commute
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:48:34.891616+00:00
-- url     : https://prove2.me/submissions/5b4eb5f1-9601-4949-9880-1de0868ce9b6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_JointShape
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_FockAct1FockAct2Commute
import Theorems.Thm_PositivityTheory_KReal_omAct_commute

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
namespace PositivityTheory.KReal
theorem _root_.solution {p q r s : ℕ} (Z : Mat p q) (W : Mat r s) :
    fockAct1 p q r s Z * fockAct2 p q r s W = fockAct2 p q r s W * fockAct1 p q r s Z := by
  refine omAct_commute (Matrix.kroneckerMap (· * ·) Z 1) (Matrix.kroneckerMap (· * ·) 1 W) ?_
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp
end PositivityTheory.KReal
