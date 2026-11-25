-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.restriction_to_affine_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:38:31.05252+00:00
-- url     : https://prove2.me/submissions/1c79fe1c-9a89-4e92-bb39-b0b53535f58f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_FreeCoordinateAffineInvertible
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_xxw_res
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_xxw_inX_inj

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
theorem _root_.solution : ResXSurjP := by
  intro E _ n' n c ρ hρ y
  obtain ⟨h1, h2⟩ := hρ
  refine ⟨resX ρ⁻¹ ∘ₗ y, ?_⟩
  have key : ∀ u : Fin n → E, resX ρ (resX ρ⁻¹ u) = u := by
    intro u
    apply xxw_inX_inj (c := c)
    rw [← xxw_res h1, ← xxw_res h2, ← LinearEquiv.mul_apply, mul_inv_cancel]
    rfl
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  exact key (y x)
end PI.TwistedEisensteinNonvanishing.W
