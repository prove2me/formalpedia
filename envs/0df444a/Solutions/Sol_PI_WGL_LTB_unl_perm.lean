-- Prove2me | solution 1 for PI.WGL.LTB.unl_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:08:50.310064+00:00
-- url     : https://prove2.me/submissions/1713f341-ed61-4269-ac30-e82003050349

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleM
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleB
import Theorems.Thm_PI_WGL_LTB_initMinor_perm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.LTB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTM
namespace PI.WGL.LTB
theorem _root_.solution {n N : ℕ} (h : n + 1 = N) {m : ℕ} (ρ : Fin m → Fin n) (hm : m ≤ N) (σ : Equiv.Perm (Fin m)) :
    unl h (ρ ∘ σ) hm = (Equiv.Perm.sign σ : ℤ) • unl h ρ hm := by
  unfold unl
  exact initMinor_perm (eRow h ∘ ρ) hm σ
end PI.WGL.LTB
