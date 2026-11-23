-- Prove2me | solution 1 for PI.WGL.LTB.initMinor_perm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:09:58.870265+00:00
-- url     : https://prove2.me/submissions/b5a2bcca-8457-4197-ac38-e0fd050e61f9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleM
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleB

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
theorem _root_.solution {R : Type*} [CommRing R] {r m s : ℕ} (I : Fin s → Fin r) (hs : s ≤ m)
    (σ : Equiv.Perm (Fin s)) :
    initMinor R (n := m) (I ∘ σ) hs = (Equiv.Perm.sign σ : ℤ) • initMinor R (n := m) I hs := by
  unfold initMinor
  first
  | (rw [zsmul_eq_mul, ← Matrix.det_permute]; rfl)
  | (rw [← Units.smul_def, ← Matrix.det_permute]; rfl)
end PI.WGL.LTB
