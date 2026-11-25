-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.xxw_tr_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:31:39.855576+00:00
-- url     : https://prove2.me/submissions/a76855a4-5800-40c0-a99b-6a398e39210a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_FreeCoordinateAffineInvertible
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_xxw_entry
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_unfolding_affine_space_invariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE
variable {E : Type} [Field E]
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution {n' c' n c : ℕ} {ρ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)} (hρ : ρ ∈ R1 E n c) (t : FC n' c' n c → E) :
    Tr ρ⁻¹ (Tr ρ t) = t := by
  have hρi : ρ⁻¹ ∈ R1 E n c := inv_mem hρ
  have e1 := unfolding_affine_space_invariant E n' c' n c ρ hρ 0 t
  have e2 := unfolding_affine_space_invariant E n' c' n c ρ⁻¹ hρi 0 (Tr ρ t)
  rw [LinearMap.comp_zero] at e1 e2
  have e3 : xx1 (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) (Tr ρ⁻¹ (Tr ρ t)) =
      xx1 (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) t := by
    rw [← e2, ← e1]
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← LinearEquiv.mul_apply, inv_mul_cancel]
    rfl
  funext f
  have h := congrFun (LinearMap.congr_fun e3 (Pi.single f.1.2 1)) f.1.1
  rw [xxw_entry, xxw_entry, dif_pos f.2, dif_pos f.2] at h
  exact h
end PI.TwistedEisensteinNonvanishing.W
