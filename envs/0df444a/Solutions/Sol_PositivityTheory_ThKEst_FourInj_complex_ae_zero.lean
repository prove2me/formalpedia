-- Prove2me | solution 1 for PositivityTheory.ThKEst.FourInj.complex_ae_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:23:08.618636+00:00
-- url     : https://prove2.me/submissions/3282ac2d-5465-4adb-a74a-e7716a6f5bd4

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_FourierInjA
import Theorems.Thm_PositivityTheory_ThKEst_FourInj_real_ae_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory BoundedContinuousFunction
open PositivityTheory PositivityTheory.ThKEst PositivityTheory.ThKEst.FourInj
variable {X A : Type} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
namespace PositivityTheory.ThKEst.FourInj
theorem _root_.solution (μ : Measure X) (e : A → X →ᵇ ℂ) (h1 : ∃ a, e a = 1) (hmul : ∀ a b, ∃ c, e c = e a * e b)
    (hstar : ∀ a, ∃ c, e c = star (e a)) (hsep : ∀ x y, x ≠ y → ∃ a, e a x ≠ e a y) {H : X → ℂ}
    (hi : Integrable H μ) (h0 : ∀ a, ∫ x, e a x * H x ∂μ = 0) : H =ᵐ[μ] 0 := by
  have hint : ∀ {k : X → ℂ}, Integrable k μ → ∀ g : X →ᵇ ℂ, Integrable (fun x => g x * k x) μ := by
    intro k hk g
    exact hk.bdd_mul (c := ‖g‖) g.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => g.norm_coe_le_norm x)
  have hic : Integrable (fun x => (starRingEnd ℂ) (H x)) μ :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hi
  have hc : ∀ a, ∫ x, e a x * (starRingEnd ℂ) (H x) ∂μ = 0 := by
    intro a
    obtain ⟨c, hc⟩ := hstar a
    have := congrArg (starRingEnd ℂ) (h0 c)
    rw [← integral_conj, map_zero, hc] at this
    simpa using this
  have hre : (fun x => (H x).re) =ᵐ[μ] 0 := by
    refine real_ae_zero μ e h1 hmul hstar hsep hi.re fun a => ?_
    have : ∀ x, (H x).re • e a x = (1 / 2 : ℂ) * (e a x * H x + e a x * (starRingEnd ℂ) (H x)) := fun x => by
      rw [← mul_add, Complex.add_conj, Complex.real_smul]; push_cast; ring
    simp only [this]
    rw [integral_const_mul, integral_add (hint hi _) (hint hic _), h0, hc]; simp
  have him : (fun x => (H x).im) =ᵐ[μ] 0 := by
    refine real_ae_zero μ e h1 hmul hstar hsep hi.im fun a => ?_
    have : ∀ x, (H x).im • e a x = (-Complex.I / 2 : ℂ) * (e a x * H x - e a x * (starRingEnd ℂ) (H x)) := fun x => by
      rw [← mul_sub, Complex.sub_conj, Complex.real_smul]; push_cast
      linear_combination ((H x).im * e a x) * Complex.I_mul_I
    simp only [this]
    rw [integral_const_mul, integral_sub (hint hi _) (hint hic _), h0, hc]; simp
  filter_upwards [hre, him] with x h1 h2
  exact Complex.ext h1 h2
end PositivityTheory.ThKEst.FourInj
