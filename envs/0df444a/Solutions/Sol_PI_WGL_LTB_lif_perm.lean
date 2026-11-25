-- Prove2me | solution 1 for PI.WGL.LTB.lif_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:36:04.315805+00:00
-- url     : https://prove2.me/submissions/d8cf3569-9e63-4482-aa52-0b4a4c4a39bb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleM
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleB
import Theorems.Thm_PI_WGL_LTB_initMinor_perm
import Theorems.Thm_PI_WGL_LTB_liftRows_perm

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
theorem _root_.solution {n N : ℕ} (h : n + 1 = N) {m : ℕ} (ρ : Fin m → Fin n) (hm : m + 1 ≤ N)
    (σ : Equiv.Perm (Fin m)) :
    lif h (ρ ∘ σ) hm = (Equiv.Perm.sign σ : ℤ) • lif h ρ hm := by
  unfold lif
  rw [liftRows_perm, initMinor_perm]
  rw [show Equiv.Perm.sign (σ.viaFintypeEmbedding Fin.castSuccEmb) = Equiv.Perm.sign σ from
    Equiv.Perm.sign_extendDomain σ _]
end PI.WGL.LTB
