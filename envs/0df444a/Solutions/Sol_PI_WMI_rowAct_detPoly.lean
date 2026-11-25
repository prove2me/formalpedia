-- Prove2me | solution 1 for PI.WMI.rowAct_detPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:10:26.197662+00:00
-- url     : https://prove2.me/submissions/514d31c7-e221-44c6-9bcb-8f585fb9b523

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_IsPolyMon
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_Assembly
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
open PI PI.WMI
open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace
namespace PI.WMI
theorem _root_.solution {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) :
    rowAct ℂ (n := N) A (detPoly N) = C A.det * detPoly N := by
  have h1 : (rowAct ℂ (n := N) A).mapMatrix
      (Matrix.of fun i j : Fin N => (X (i, j) : MvPolynomial (Fin N × Fin N) ℂ)) =
      (C : ℂ →+* MvPolynomial (Fin N × Fin N) ℂ).mapMatrix A *
        Matrix.of fun i j : Fin N => (X (i, j) : MvPolynomial (Fin N × Fin N) ℂ) := by
    ext i j
    simp [rowAct, Matrix.mul_apply]
  rw [detPoly, AlgHom.map_det, h1, Matrix.det_mul, ← RingHom.map_det]
end PI.WMI
