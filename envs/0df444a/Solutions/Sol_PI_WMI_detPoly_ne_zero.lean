-- Prove2me | solution 1 for PI.WMI.detPoly_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:10:21.324799+00:00
-- url     : https://prove2.me/submissions/d1c13b77-c002-4210-a62f-56c3b4c1cce4

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
theorem _root_.solution (N : ℕ) : detPoly N ≠ 0 := by
  intro h
  have := congrArg (eval (fun ij : Fin N × Fin N => (1 : Matrix (Fin N) (Fin N) ℂ) ij.1 ij.2)) h
  rw [detPoly, RingHom.map_det, map_zero] at this
  have hm : (eval (fun ij : Fin N × Fin N => (1 : Matrix (Fin N) (Fin N) ℂ) ij.1 ij.2)).mapMatrix
      (Matrix.of fun i j : Fin N => (X (i, j) : MvPolynomial (Fin N × Fin N) ℂ)) = 1 := by
    ext i j; simp
  rw [hm, det_one] at this
  exact one_ne_zero this
end PI.WMI
