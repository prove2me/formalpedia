-- Prove2me | solution 1 for PI.WGL.XiB.xi_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:13:38.500069+00:00
-- url     : https://prove2.me/submissions/4ba80bd5-bb14-4659-98a5-f41de1141381

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_RowsZStrictMono
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_EvalInitMinorNormLe
import Theorems.Thm_PI_WGL_XiB_eval_initMinor_norm_le
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
theorem _root_.solution {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)
    (x : Matrix (Fin N) (Fin N) ℂ) (hx : x ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    ‖MvPolynomial.eval (fun v : Fin N × Fin N => x v.1 v.2) (xi ℂ h lam sg)‖ ≤ 1 := by
  unfold xi
  rw [map_prod, norm_prod]
  apply Finset.prod_le_one (fun i _ => norm_nonneg _)
  intro i _
  rw [map_mul, map_pow, map_pow, norm_mul, norm_pow, norm_pow]
  apply mul_le_one₀ (pow_le_one₀ (norm_nonneg _) ?_) (pow_nonneg (norm_nonneg _) _)
    (pow_le_one₀ (norm_nonneg _) ?_)
  · rw [XiA.lpMinor_eq]
    exact eval_initMinor_norm_le x hx _ (Fin.castLE_injective _) _
  · exact eval_initMinor_norm_le x hx _ (XiA.rowsZ_strictMono h i).injective _
end PI.WGL.XiB
