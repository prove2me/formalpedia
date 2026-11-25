-- Prove2me | solution 1 for PI.WGL.XiB.xi_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:39:58.789863+00:00
-- url     : https://prove2.me/submissions/86980a06-1906-4f00-8f0a-f9a88f4719a2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_RowsZStrictMono
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_EvalInitMinorNormLe
import Theorems.Thm_PI_WGL_XiB_initMinor_ne
import Theorems.Thm_PI_WGL_XiA_lpMinor_eq
import Theorems.Thm_PI_WGL_XiA_rowsZ_strictMono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.XiB
open Formalism.BasicNotions MvPolynomial
namespace PI.WGL.XiB
theorem _root_.solution {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : xi ℂ h lam sg ≠ 0 := by
  unfold xi
  rw [Finset.prod_ne_zero_iff]
  intro i _
  apply mul_ne_zero
  · apply pow_ne_zero
    rw [XiA.lpMinor_eq]
    exact initMinor_ne _ (Fin.castLE_injective _) _
  · apply pow_ne_zero
    exact initMinor_ne _ (XiA.rowsZ_strictMono h i).injective _
end PI.WGL.XiB
