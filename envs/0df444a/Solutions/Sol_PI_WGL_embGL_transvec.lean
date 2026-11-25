-- Prove2me | solution 1 for PI.WGL.embGL_transvec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:52:28.043047+00:00
-- url     : https://prove2.me/submissions/ec0a3b2b-c7a3-47d6-a160-9b8488463e8c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_ConstructionA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliEqv
import Theorems.Thm_PI_WGL_embGL_cc
import Theorems.Thm_PI_WGL_embGL_lc
import Theorems.Thm_PI_WGL_embGL_cl
import Theorems.Thm_PI_WGL_embGL_ll
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
theorem _root_.solution {n : ℕ} (g : GL (Fin n) ℂ) (a b : Fin n) (t : ℂ)
    (hg : (g : Matrix (Fin n) (Fin n) ℂ) = 1 + Matrix.single a b t) :
    ((embGL ℂ n (n + 1) rfl g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).transpose =
      1 + Matrix.single b.castSucc a.castSucc t := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [Matrix.transpose_apply, embGL_ll, Matrix.single_apply]
    | cast j =>
      simp [Matrix.transpose_apply, embGL_cl, Matrix.one_apply]
      exact fun h => Fin.castSucc_ne_last j h.symm
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp [Matrix.transpose_apply, embGL_lc, Matrix.single_apply, Matrix.one_apply]
    | cast j =>
      rw [Matrix.transpose_apply, embGL_cc, hg]
      simp [Matrix.single_apply, Matrix.one_apply, eq_comm, and_comm]
end PI.WGL
