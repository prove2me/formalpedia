-- Prove2me | solution 1 for PI.VolStabW.chLift_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:32:47.037706+00:00
-- url     : https://prove2.me/submissions/6919dd47-193e-4667-812f-8e8599f70c8e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensSAChar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensChLift
import Theorems.Thm_PI_VolStabW_ChLiftW_lift_place
import Theorems.Thm_PI_VolStabW_ChLiftW_addChar_sum
import Theorems.Thm_PI_VolStabW_sgl_add
import Theorems.Thm_PI_VolStabW_sgl_zero
import Theorems.Thm_PI_VolStabW_continuous_sgl
import Theorems.Thm_PI_VolStabW_sum_sgl

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
open PI PI.VolStabW
open ChLiftW
namespace PI.VolStabW
theorem _root_.solution : ChLift := by
  intro F _ _ χ hχ
  have hloc : ∀ v : InfinitePlace F, ∃ ℓ : v.Completion →+ ℂ, Continuous ℓ ∧
      ∀ t, χ (sgl v t) = exp (ℓ t) := fun v =>
    lift_place v (fun t => χ (sgl v t)) (hχ.comp (continuous_sgl v))
      (fun x y => by simp only [sgl_add, AddChar.map_add_eq_mul])
      (by simp only [sgl_zero, AddChar.map_zero_eq_one])
  choose ℓv hℓc hℓ using hloc
  let ℓ : InfiniteAdeleRing F →+ ℂ := AddMonoidHom.mk' (fun x => ∑ v, ℓv v (x v)) (fun a b => by
    show ∑ v, ℓv v (a v + b v) = _
    simp [map_add, Finset.sum_add_distrib])
  refine ⟨ℓ, ?_, fun x => ?_⟩
  · show Continuous (fun x : InfiniteAdeleRing F => ∑ v, ℓv v (x v))
    exact continuous_finsetSum _ fun v _ => (hℓc v).comp (continuous_apply v)
  · conv_lhs => rw [← sum_sgl x]
    rw [addChar_sum]
    show _ = exp (∑ v, ℓv v (x v))
    rw [Complex.exp_sum]
    exact Finset.prod_congr rfl fun v _ => hℓ v (x v)
end PI.VolStabW
