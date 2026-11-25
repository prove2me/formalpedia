-- Prove2me | solution 1 for PI.VolStabS.ChLiftW.lift_homeo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:09:10.815244+00:00
-- url     : https://prove2.me/submissions/d1d14bba-1436-4bec-9a6d-75829e64a663

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensSAChar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensChLift
import Theorems.Thm_PI_VolStabS_ChLiftW_lift_normed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Complex
open PI PI.VolStabS
open PI.VolStabS.ChLiftW
namespace PI.VolStabS.ChLiftW
theorem _root_.solution {X W : Type*} [AddCommGroup X] [TopologicalSpace X] [NormedAddCommGroup W]
    [NormedSpace ℝ W] (e : X ≃ₜ W) (he : ∀ x y, e (x + y) = e x + e y) (χ : X → ℂ)
    (hc : Continuous χ) (hadd : ∀ x y, χ (x + y) = χ x * χ y) (h0 : χ 0 = 1) :
    ∃ ℓ : X →+ ℂ, Continuous ℓ ∧ ∀ x, χ x = exp (ℓ x) := by
  have hes : ∀ a b, e.symm (a + b) = e.symm a + e.symm b := fun a b => by
    apply e.injective
    rw [he]; simp
  have he0 : e.symm 0 = 0 := by
    have := hes 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this
  obtain ⟨ℓ', hℓc, hℓ⟩ := lift_normed (χ ∘ e.symm) (hc.comp e.symm.continuous)
    (fun a b => by simp only [Function.comp, hes, hadd]) (by simp [he0, h0])
  refine ⟨ℓ'.comp (AddMonoidHom.mk' e he), hℓc.comp e.continuous, fun x => ?_⟩
  have := hℓ (e x)
  simpa using this
end PI.VolStabS.ChLiftW
