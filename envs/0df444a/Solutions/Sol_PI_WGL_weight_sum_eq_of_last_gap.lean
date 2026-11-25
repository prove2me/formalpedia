-- Prove2me | solution 1 for PI.WGL.weight_sum_eq_of_last_gap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:24:09.005213+00:00
-- url     : https://prove2.me/submissions/6328aaf6-17a4-4b54-9a48-31c85ce850d6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDecomp
import Theorems.Thm_PI_WGL_degree_sub_det_shift_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
namespace PI.WGL
theorem _root_.solution {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (mu sg : DomWeight n)
    (hmu : Interlace h lam mu) (hsg : Interlace h lam sg) (hd : dLast lam mu = dLast lam sg) :
    wsum mu = wsum sg := by
  have h1 := degree_sub_det_shift_nonneg h lam mu hmu
  have h2 := degree_sub_det_shift_nonneg h lam sg hsg
  unfold dLast at hd
  have h3 : degZ lam mu - lam.detShift = degZ lam sg - lam.detShift := by
    rw [← Int.toNat_of_nonneg h1, ← Int.toNat_of_nonneg h2, hd]
  unfold degZ at h3
  linarith
end PI.WGL
