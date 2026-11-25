-- Prove2me | solution 1 for PI.WGL.XiA.rowAct_initMinor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:15:44.032594+00:00
-- url     : https://prove2.me/submissions/428dd1f8-0cf4-49e3-a32d-3b7e79ad8c5b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_MultisetProdNormLeOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_RowsZStrictMono
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_WGL_XiU_sum_comp_eq
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
open PI PI.WGL PI.WGL.XiA
open Formalism.BasicNotions MvPolynomial
namespace PI.WGL.XiA
theorem _root_.solution {N s : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (I : Fin s → Fin N) (hI : StrictMono I)
    (hs : s ≤ N) (hG : ∀ a b : Fin N, a < b → G b a = 0)
    (hcl : ∀ p b, G b (I p) ≠ 0 → b ∈ Set.range I) :
    Formalism.GradedWeylDivisibility.rowAct ℂ G.transpose (Formalism.GradedWeylDivisibility.initMinor ℂ (n := N) I hs) =
      C (∏ p, G (I p) (I p)) * Formalism.GradedWeylDivisibility.initMinor ℂ (n := N) I hs := by
  classical
  set B : Matrix (Fin s) (Fin s) ℂ := Matrix.of fun p p' => G (I p') (I p) with hB
  have hmat : ((Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) G.transpose : MvPolynomial (Fin N × Fin N) ℂ →+* MvPolynomial (Fin N × Fin N) ℂ)).mapMatrix
      (Matrix.of fun p q : Fin s => (X (I p, Fin.castLE hs q) : MvPolynomial (Fin N × Fin N) ℂ)) =
      (C : ℂ →+* MvPolynomial (Fin N × Fin N) ℂ).mapMatrix B *
      (Matrix.of fun p q : Fin s => (X (I p, Fin.castLE hs q) : MvPolynomial (Fin N × Fin N) ℂ)) := by
    ext p q
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply, hB,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Formalism.GradedWeylDivisibility.rowAct, aeval_X, Matrix.transpose_apply]
    rw [XiU.sum_comp_eq I hI.injective]
    intro b hb
    have : G b (I p) = 0 := by
      by_contra hne
      exact hb (hcl p b hne)
    simp [this]
  have hBdet : B.det = ∏ p, G (I p) (I p) := by
    rw [Matrix.det_of_isLowerTriangular B]
    · rfl
    · intro p p' hpp'
      exact hG _ _ (hI (by simpa using hpp'))
  have hdet := RingHom.map_det ((Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) G.transpose :
      MvPolynomial (Fin N × Fin N) ℂ →+* MvPolynomial (Fin N × Fin N) ℂ))
    (Matrix.of fun p q : Fin s => (X (I p, Fin.castLE hs q) : MvPolynomial (Fin N × Fin N) ℂ))
  rw [RingHom.coe_coe] at hdet
  show Formalism.GradedWeylDivisibility.rowAct ℂ G.transpose
      (Matrix.of fun p q : Fin s => (X (I p, Fin.castLE hs q) : MvPolynomial (Fin N × Fin N) ℂ)).det =
    C (∏ p, G (I p) (I p)) * (Matrix.of fun p q : Fin s => (X (I p, Fin.castLE hs q) : MvPolynomial (Fin N × Fin N) ℂ)).det
  rw [hdet, hmat, Matrix.det_mul, ← RingHom.map_det, hBdet]
end PI.WGL.XiA
