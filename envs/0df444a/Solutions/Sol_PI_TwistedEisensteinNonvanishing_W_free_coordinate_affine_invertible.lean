-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.free_coordinate_affine_invertible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:38:23.926024+00:00
-- url     : https://prove2.me/submissions/da373f19-328e-4ea5-a34b-1384094b38df

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_FreeCoordinateAffineInvertible
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_xxw_tr_eq
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_xxw_tr_inv

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
theorem _root_.solution : TrAffP := by
  intro E _ n' c' n c ρ hρ
  have hρi : ρ⁻¹ ∈ R1 E n c := inv_mem hρ
  have key : ∀ σ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E), σ ∈ R1 E n c →
      ∀ t : FC n' c' n c → E, xxwLin σ⁻¹ (xxwLin σ t) = t := by
    intro σ hσ t
    have h1 := xxw_tr_inv hσ t
    have h0 := xxw_tr_inv hσ (0 : FC n' c' n c → E)
    rw [xxw_tr_eq σ⁻¹, xxw_tr_eq σ t, map_add] at h1
    rw [xxw_tr_eq σ⁻¹] at h0
    calc xxwLin σ⁻¹ (xxwLin σ t) = (xxwLin σ⁻¹ (xxwLin σ t) + xxwLin σ⁻¹ (Tr σ 0) + Tr σ⁻¹ 0) -
          (xxwLin σ⁻¹ (Tr σ 0) + Tr σ⁻¹ 0) := by abel
      _ = t - 0 := by rw [h1, h0]
      _ = t := sub_zero t
  refine ⟨{ xxwLin ρ with invFun := xxwLin ρ⁻¹, left_inv := key ρ hρ, right_inv := ?_ },
    fun t => xxw_tr_eq ρ t⟩
  intro t
  have := key ρ⁻¹ hρi t
  rwa [inv_inv] at this
end PI.TwistedEisensteinNonvanishing.W
