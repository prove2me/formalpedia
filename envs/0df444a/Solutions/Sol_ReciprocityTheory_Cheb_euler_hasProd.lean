-- Prove2me | solution 1 for ReciprocityTheory.Cheb.euler_hasProd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:33:31.113329+00:00
-- url     : https://prove2.me/submissions/e6245122-bcae-44b5-8c0e-25895d18838d

import Definitions.Def_ReciprocityTheory_Chebotarev_EulerFin
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerLim
import Theorems.Thm_ReciprocityTheory_Cheb_exists_smooth
import Theorems.Thm_ReciprocityTheory_Cheb_Smooth_mono
import Theorems.Thm_ReciprocityTheory_Cheb_euler_finite


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
theorem _root_.solution {E : Type} [Field E] [NumberField E] (f : Ideal (𝓞 E) → ℂ) (hf1 : f 1 = 1)
    (hmul : ∀ a b : Ideal (𝓞 E), f (a * b) = f a * f b)
    (hsum : Summable (fun a : NZIdeal E => ‖f a.1‖)) (hlt : ∀ q : Prm E, ‖f q.asIdeal‖ < 1) :
    HasProd (fun q : Prm E => (1 - f q.asIdeal)⁻¹) (∑' a : NZIdeal E, f a.1) := by
  unfold HasProd
  simp only [SummationFilter.unconditional_filter]
  have key : (fun S : Finset (Prm E) => ∏ q ∈ S, (1 - f q.asIdeal)⁻¹) =
      fun S => ∑' a : NZIdeal E, Set.indicator {a : NZIdeal E | Smooth S a.1} (fun a => f a.1) a := by
    funext S
    exact (euler_finite f hf1 hmul hsum hlt S).tsum_eq.symm
  rw [key]
  refine tendsto_tsum_of_dominated_convergence (bound := fun a : NZIdeal E => ‖f a.1‖) hsum ?_ ?_
  · intro a
    obtain ⟨S0, hS0⟩ := exists_smooth a
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop S0] with S hS
    have : a ∈ {a : NZIdeal E | Smooth S a.1} := Smooth.mono hS0 hS
    rw [Set.indicator_of_mem this]
  · exact Eventually.of_forall fun S a => norm_indicator_le_norm_self _ _
end ReciprocityTheory.Cheb
