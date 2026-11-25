-- Prove2me | solution 1 for PI.Dv.IdxW.lenS_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:43:39.830705+00:00
-- url     : https://prove2.me/submissions/b40bcff2-3565-4899-b6a5-444df400a9f9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ElementDenominator
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IndexCalculation_IsLocalizedModuleToSpan
import Theorems.Thm_PI_Dv_IdxW_lenS_exact
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
theorem _root_.solution (P N M : Submodule R V) (hPN : P ≤ N) (hNM : N ≤ M) :
    lenS S M P = lenS S M N + lenS S N P := by
  let f : (↥N ⧸ P.comap N.subtype) →ₗ[R] (↥M ⧸ P.comap M.subtype) :=
    Submodule.mapQ _ _ (Submodule.inclusion hNM) (by
      intro x hx
      simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_inclusion] at hx ⊢
      exact hx)
  let g : (↥M ⧸ P.comap M.subtype) →ₗ[R] (↥M ⧸ N.comap M.subtype) :=
    Submodule.mapQ _ _ LinearMap.id (fun x hx => hPN hx)
  have key := lenS_exact S f g ?_ ?_ ?_
  · unfold lenS
    rw [key, add_comm]
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro y hy
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      rw [LinearMap.mem_ker] at hy
      dsimp only [f] at hy
      rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hy
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
      exact hy
  · intro z
    induction z using Submodule.Quotient.induction_on with
    | H x => exact ⟨Submodule.Quotient.mk x, rfl⟩
  · intro y
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      constructor
      · intro hy
        dsimp only [g] at hy
        rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hy
        exact ⟨Submodule.Quotient.mk ⟨x, hy⟩, rfl⟩
      · rintro ⟨w, hw⟩
        rw [← hw]
        induction w using Submodule.Quotient.induction_on with
        | H z =>
          dsimp only [f, g]
          rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
          exact z.2
end PI.Dv.IdxW
