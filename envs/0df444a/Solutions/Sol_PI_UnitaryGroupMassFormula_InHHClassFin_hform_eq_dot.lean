-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.InHHClassFin.hform_eq_dot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:40:33.205414+00:00
-- url     : https://prove2.me/submissions/54ca7dc6-2dd8-4985-8201-fd8ef4249e54

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_HformSumRight
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
open NumberField Matrix Formalism.UG PI.InHHClassFin
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.InHHClassFin
variable {I : Formalism.MainNotions.S.AutInst} {S : Set (Fin I.n → I.E)}
namespace PI.UnitaryGroupMassFormula.InHHClassFin
theorem _root_.solution {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J : Matrix n n A) (x y : n → A) : hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp only [hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]
end PI.UnitaryGroupMassFormula.InHHClassFin
