-- Prove2me | solution 1 for PI.Dv.IdxW.length_quot_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:38:21.768744+00:00
-- url     : https://prove2.me/submissions/f2a7ea36-70b4-47fa-aa14-fe3418513903

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ElementDenominator
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IndexCalculation_IsLocalizedModuleToSpan
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.IdxW
open Module
variable {R : Type*} [CommRing R] (S : Submonoid R)
variable {V : Type*} [AddCommGroup V] [Module R V]
namespace PI.Dv.IdxW
theorem _root_.solution {A : Type*} [CommRing A] [StrongRankCondition A] (J : Ideal A)
    (N : Type*) [AddCommGroup N] [Module A N] [Module.Free A N] [Module.Finite A N] :
    Module.length A (N ⧸ J • (⊤ : Submodule A N)) =
      (Module.finrank A N : ℕ∞) * Module.length A (A ⧸ J) := by
  let b := Module.finBasis A N
  let e : (N ⧸ J • (⊤ : Submodule A N)) ≃ₗ[A] (Fin (Module.finrank A N) → A ⧸ J) :=
    (TensorProduct.quotTensorEquivQuotSMul N J).symm ≪≫ₗ
      TensorProduct.congr (LinearEquiv.refl A (A ⧸ J)) b.equivFun ≪≫ₗ
        TensorProduct.piScalarRight A A (A ⧸ J) (Fin (Module.finrank A N))
  rw [e.length_eq, Module.length_pi_of_fintype]
  simp
end PI.Dv.IdxW
