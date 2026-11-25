-- Prove2me | solution 1 for PositivityTheory.ThKEst.LinDerPf.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:59:16.016437+00:00
-- url     : https://prove2.me/submissions/847a4359-53d0-4488-be17-587f9c3a4e02

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_LinDerA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKEst PositivityTheory.ThKEst.LinDerPf
open Filter Topology Asymptotics
variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
namespace PositivityTheory.ThKEst.LinDerPf
theorem _root_.solution (β : Multiplicative ℝ →* H) (hβ : Continuous β) (f f' : H → ℂ) (hf' : Continuous f')
    (hd : ∀ h, HasDerivAt (fun t : ℝ => f (h * β (Multiplicative.ofAdd t))) (f' h) 0)
    (p : ℝ → H) (hp : ContinuousAt p 0) (u : ℝ → ℝ) (u' : ℝ) (hu : HasDerivAt u u' 0) (hu0 : u 0 = 0)
    (D : ℂ) (hD : HasDerivAt (fun t => f (p t)) D 0) :
    HasDerivAt (fun t => f (p t * β (Multiplicative.ofAdd (u t)))) (D + u' * f' (p 0)) 0 := by
  have hd' : ∀ h (v : ℝ), HasDerivAt (fun t : ℝ => f (h * β (Multiplicative.ofAdd t)))
      (f' (h * β (Multiplicative.ofAdd v))) v := fun h v => by
    have h1 := hd (h * β (Multiplicative.ofAdd v))
    have h2 : HasDerivAt (fun t : ℝ => f (h * β (Multiplicative.ofAdd v) * β (Multiplicative.ofAdd t)))
        (f' (h * β (Multiplicative.ofAdd v))) (v - v) := by rwa [sub_self]
    have h3 := h2.comp_sub_const v v
    refine h3.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    simp only [mul_assoc, ← map_mul, ← ofAdd_add, add_sub_cancel]
  set R : ℝ → ℂ := fun t => f (p t * β (Multiplicative.ofAdd (u t))) - f (p t) - u t * f' (p 0) with hR
  have hc : Continuous fun z : H × ℝ => f' (z.1 * β (Multiplicative.ofAdd z.2)) :=
    hf'.comp (continuous_fst.mul (hβ.comp (continuous_ofAdd.comp continuous_snd)))
  have ho : R =o[𝓝 0] u := by
    refine isLittleO_iff.2 fun ε hε => ?_
    have h1 : ∀ᶠ z : H × ℝ in 𝓝 (p 0, 0), ‖f' (z.1 * β (Multiplicative.ofAdd z.2)) - f' (p 0)‖ ≤ ε := by
      have h2 := (hc.tendsto (p 0, 0))
      simp only [ofAdd_zero, map_one, mul_one] at h2
      filter_upwards [h2 (Metric.closedBall_mem_nhds _ hε)] with z hz
      simpa [dist_eq_norm] using hz
    rw [nhds_prod_eq] at h1
    obtain ⟨U, hU, V, hV, hUV⟩ := Filter.eventually_prod_iff.1 h1
    obtain ⟨δ, hδ, hδV⟩ := Metric.eventually_nhds_iff_ball.1 hV
    have hu1 : ∀ᶠ t in 𝓝 (0 : ℝ), u t ∈ Metric.ball (0 : ℝ) δ := by
      have := hu.continuousAt.tendsto
      rw [hu0] at this
      exact this (Metric.ball_mem_nhds _ hδ)
    filter_upwards [hp.tendsto hU, hu1] with t ht1 ht2
    have h3 := (convex_ball (0 : ℝ) δ).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun v : ℝ => f (p t * β (Multiplicative.ofAdd v)) - v * f' (p 0))
      (f' := fun v : ℝ => f' (p t * β (Multiplicative.ofAdd v)) - f' (p 0)) (C := ε)
      (fun v _ => by
        have h4 : HasDerivAt (fun v : ℝ => (v : ℂ) * f' (p 0)) (f' (p 0)) v := by
          simpa using (Complex.ofRealCLM.hasDerivAt (x := v)).mul_const (f' (p 0))
        exact ((hd' (p t) v).sub h4).hasDerivWithinAt)
      (fun v hv => hUV ht1 (hδV v hv)) (Metric.mem_ball_self hδ) ht2
    simp only [ofAdd_zero, map_one, mul_one, Complex.ofReal_zero, zero_mul, sub_zero] at h3
    have e : R t = f (p t * β (Multiplicative.ofAdd (u t))) - u t * f' (p 0) - f (p t) := by
      simp only [hR]
      ring
    rw [e]
    exact h3
  have hO : u =O[𝓝 0] fun t : ℝ => t - 0 := by
    have := hu.isBigO_sub
    simpa [hu0] using this
  have hR0 : HasDerivAt R 0 0 := by
    rw [hasDerivAt_iff_isLittleO]
    have : R 0 = 0 := by simp [hR, hu0]
    simpa [this] using ho.trans_isBigO hO
  have h5 : HasDerivAt (fun t : ℝ => (u t : ℂ) * f' (p 0)) (u' * f' (p 0)) 0 :=
    hu.ofReal_comp.mul_const _
  have h6 := (hR0.add hD).add h5
  rw [zero_add] at h6
  refine h6.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp only [hR, Pi.add_apply]
  ring
end PositivityTheory.ThKEst.LinDerPf
