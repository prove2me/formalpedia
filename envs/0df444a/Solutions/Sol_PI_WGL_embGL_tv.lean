-- Prove2me | solution 1 for PI.WGL.embGL_tv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:08:50.498804+00:00
-- url     : https://prove2.me/submissions/0a884857-76c8-4aff-b1bb-61a1017c4183

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftEqvDiv
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
theorem _root_.solution {n N : ℕ} (h : n + 1 = N) (a b : Fin n) (hab : a ≠ b) (t : ℂ) :
    ((PI.embGL ℂ n N h (tvU a b hab t) : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      Formalism.UG.P.wlocal_E (eRow h a) (eRow h b) t := by
  subst h
  have he : ∀ x : Fin n, eRow (rfl : n + 1 = n + 1) x = Fin.castSucc x := fun x => Fin.ext rfl
  have hl : ∀ x : Fin n, (Fin.last n = Fin.castSucc x) ↔ False :=
    fun x => ⟨fun e => (Fin.castSucc_lt_last x).ne' e, False.elim⟩
  ext i j
  simp only [he]
  simp [PI.embGL, PI.blkHom, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, tvU]
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp [Formalism.UG.P.wlocal_E, hl]
end PI.WGL
