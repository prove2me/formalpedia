-- Prove2me | solution 1 for PI.VolStabSW.ChLiftW.lift_homeo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:58:01.195832+00:00
-- url     : https://prove2.me/submissions/19452607-5972-48ab-8f3c-7dad0bf373ef

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensSAChar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensChLift
import Theorems.Thm_PI_VolStabSW_ChLiftW_lift_normed

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
open PI PI.VolStabSW
open PI.VolStabSW.ChLiftW
namespace PI.VolStabSW.ChLiftW
theorem _root_.solution {X W : Type*} [AddCommGroup X] [TopologicalSpace X] [NormedAddCommGroup W]
    [NormedSpace ℝ W] (e : X ≃ₜ W) (he : ∀ x y, e (x + y) = e x + e y) (χ : X → ℂ)
    (hc : Continuous χ) (hadd : ∀ x y, χ (x + y) = χ x * χ y) (h0 : χ 0 = 1) :
    ∃ ℓ : X →+ ℂ, Continuous ℓ ∧ ∀ x, χ x = exp (ℓ x) := by
  have he0 : e 0 = 0 := by simpa using he 0 0
  have hs0 : e.symm 0 = 0 := by rw [← he0, Homeomorph.symm_apply_apply]
  have hsadd : ∀ w w' : W, e.symm (w + w') = e.symm w + e.symm w' := by
    intro w w'
    apply e.injective
    rw [he, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  obtain ⟨ℓ', hℓc, hℓ⟩ := lift_normed (fun w => χ (e.symm w)) (hc.comp e.symm.continuous)
    (fun w w' => by simp only [hsadd, hadd]) (by simp only [hs0, h0])
  refine ⟨AddMonoidHom.mk' (fun x => ℓ' (e x)) (fun x y => by simp only [he, map_add]),
    hℓc.comp e.continuous, fun x => ?_⟩
  have h1 := hℓ (e x)
  simp only [Homeomorph.symm_apply_apply] at h1
  exact h1
end PI.VolStabSW.ChLiftW
