-- Prove2me | solution 1 for PI.WGL.det_one_add_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:12.745484+00:00
-- url     : https://prove2.me/submissions/c37bc7f5-dd99-42b4-b399-4a1d1aa03074

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_ConstructionA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliEqv
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
open PI PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
namespace PI.WGL
theorem _root_.solution {n : ℕ} (a b : Fin n) (t : ℂ) :
    (1 + Matrix.single a b t).det = if a = b then t + 1 else 1 := by
  by_cases hab : a = b
  · subst hab
    have hD : (1 + Matrix.single a a t) = Matrix.diagonal (fun i => if i = a then 1 + t else 1) := by
      ext i j
      by_cases hij : i = j
      · subst hij; by_cases hia : i = a
        · subst hia; simp
        · simp [hia, Ne.symm hia]
      · simp [hij, Matrix.single_apply]
        intro h1 h2; exact absurd (h1.symm.trans h2) hij
    rw [hD, Matrix.det_diagonal, Finset.prod_ite_eq']
    simp [add_comm]
  · have := Matrix.det_transvection_of_ne a b hab t
    unfold Matrix.transvection at this
    rw [this, if_neg hab]
end PI.WGL
