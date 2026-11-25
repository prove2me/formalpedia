-- Prove2me | solution 1 for PI.WGL.XiB.initMinor_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:14:16.044045+00:00
-- url     : https://prove2.me/submissions/410ea4bf-ecee-4a67-aaca-c66b3278ad27

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_RowsZStrictMono
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_EvalInitMinorNormLe
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.XiB
open Formalism.BasicNotions MvPolynomial
namespace PI.WGL.XiB
theorem _root_.solution {N s : ℕ} (I : Fin s → Fin N) (hI : Function.Injective I) (hs : s ≤ N) :
    Formalism.GradedWeylDivisibility.initMinor ℂ (n := N) I hs ≠ 0 := by
  classical
  intro h0
  let v : Fin N × Fin N → ℂ := fun w => if ∃ p : Fin s, I p = w.1 ∧ Fin.castLE hs p = w.2 then 1 else 0
  have h1 := congrArg (MvPolynomial.eval v) h0
  rw [map_zero] at h1
  unfold Formalism.GradedWeylDivisibility.initMinor at h1
  rw [RingHom.map_det] at h1
  have hM : (MvPolynomial.eval v).mapMatrix
      (Matrix.of fun p q : Fin s => (X (I p, Fin.castLE hs q) : MvPolynomial (Fin N × Fin N) ℂ)) = 1 := by
    ext p q
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.eval_X,
      Matrix.one_apply, v]
    by_cases hpq : p = q
    · subst hpq
      rw [if_pos ⟨p, rfl, rfl⟩, if_pos rfl]
    · rw [if_neg hpq, if_neg]
      rintro ⟨p', h2, h3⟩
      have h4 : p' = p := hI h2
      subst h4
      apply hpq
      have h5 := congrArg Fin.val h3
      simp only [Fin.coe_castLE] at h5
      exact Fin.ext h5
  rw [hM, Matrix.det_one] at h1
  exact one_ne_zero h1
end PI.WGL.XiB
