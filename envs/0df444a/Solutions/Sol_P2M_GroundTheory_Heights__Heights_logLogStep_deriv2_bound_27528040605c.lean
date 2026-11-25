-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_logLogStep_deriv2_bound_27528040605c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:19:18.811651+00:00
-- url     : https://prove2.me/submissions/19746f60-f253-4eff-91cc-eef8553eb999

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLogLogCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLogLogCutHessDeriv
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_smoothTransition_deriv_bound_7ff97014ece1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_logLogStep_arith_994d7a824460

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Filter Topology
open scoped ContDiff
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, 1 ≤ c → ∀ t : ℝ, t < 0 →
      ContDiffAt ℝ 2 (fun x => cutStep (Real.log (-x) / c)) t ∧
      ContDiffAt ℝ 2 (fun x => cutStep (Real.log (-x) / c) ^ 2 / 2) t ∧
      |deriv (deriv fun x => cutStep (Real.log (-x) / c)) t| ≤ K / (c * t ^ 2) ∧
      |deriv (deriv fun x => cutStep (Real.log (-x) / c) ^ 2 / 2) t| ≤ K / (c * t ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := smoothTransition_deriv_bound
  refine ⟨6 * C + 4 * C ^ 2, by positivity, fun c hc t ht => ?_⟩
  have hc0 : 0 < c := by linarith
  set σ := Real.smoothTransition with hσdef
  have hsm : ContDiff ℝ ∞ σ := Real.smoothTransition.contDiff
  obtain ⟨hd0, h1⟩ := contDiff_infty_iff_deriv.1 hsm
  obtain ⟨hd1, -⟩ := contDiff_infty_iff_deriv.1 h1
  let u : ℝ → ℝ := fun x => 2 - 2 * (Real.log (-x) / c)
  let u' : ℝ → ℝ := fun x => -(2 * (x⁻¹ / c))
  let u'' : ℝ → ℝ := fun x => -(2 * (-(x ^ 2)⁻¹ / c))
  have hu : ∀ x, x < 0 → HasDerivAt u (u' x) x := by
    intro x hx
    have hl : HasDerivAt (fun x => Real.log (-x)) x⁻¹ x := by
      have := (hasDerivAt_neg x).log (by simpa using hx.ne)
      rwa [neg_div_neg_eq, one_div] at this
    exact ((hl.div_const c).const_mul 2).const_sub 2
  have hu' : ∀ x, x < 0 → HasDerivAt u' (u'' x) x := fun x hx =>
    (((hasDerivAt_inv hx.ne).div_const c).const_mul 2).neg
  let F : ℝ → ℝ := fun x => cutStep (Real.log (-x) / c)
  let G : ℝ → ℝ := fun x => deriv σ (u x) * u' x
  have hF : ∀ x, x < 0 → HasDerivAt F (G x) x := fun x hx =>
    (hd0 (u x)).hasDerivAt.comp x (hu x hx)
  have hG : HasDerivAt G (deriv (deriv σ) (u t) * u' t * u' t + deriv σ (u t) * u'' t) t :=
    ((hd1 (u t)).hasDerivAt.comp t (hu t ht)).mul (hu' t ht)
  have evF : deriv F =ᶠ[𝓝 t] G := by
    filter_upwards [Iio_mem_nhds ht] with x hx
    exact (hF x hx).deriv
  have hF2 : deriv (deriv F) t = deriv (deriv σ) (u t) * u' t * u' t + deriv σ (u t) * u'' t :=
    (hG.congr_of_eventuallyEq evF).deriv
  have hH : ∀ x, x < 0 → HasDerivAt (fun x => F x ^ 2 / 2) (F x * G x) x := by
    intro x hx
    have := ((hF x hx).fun_mul (hF x hx)).div_const 2
    exact (this.congr_deriv (by ring)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => by ring)
  have evH : deriv (fun x => F x ^ 2 / 2) =ᶠ[𝓝 t] fun x => F x * G x := by
    filter_upwards [Iio_mem_nhds ht] with x hx
    exact (hH x hx).deriv
  have hH2 : deriv (deriv fun x => F x ^ 2 / 2) t =
      G t * G t + F t * (deriv (deriv σ) (u t) * u' t * u' t + deriv σ (u t) * u'' t) :=
    (((hF t ht).fun_mul hG).congr_of_eventuallyEq evH).deriv
  have hucd : ContDiffAt ℝ 2 u t :=
    contDiffAt_const.sub (contDiffAt_const.mul ((contDiffAt_id.neg.log (by simpa using ht.ne)).div_const c))
  have hFcd : ContDiffAt ℝ 2 F t := (Real.smoothTransition.contDiffAt (n := 2)).comp t hucd
  have hf : |F t| ≤ 1 := by
    show |Real.smoothTransition (u t)| ≤ 1
    exact abs_le.2 ⟨by linarith [Real.smoothTransition.nonneg (u t)], Real.smoothTransition.le_one (u t)⟩
  obtain ⟨b1, b2⟩ := logLogStep_arith (p := deriv σ (u t)) (q := deriv (deriv σ) (u t)) hC0 hc ht.ne
    (hC _).1 (hC _).2 hf rfl rfl
  refine ⟨hFcd, (hFcd.pow 2).div_const 2, ?_, ?_⟩
  · rw [show deriv (deriv fun x => cutStep (Real.log (-x) / c)) t = _ from hF2]; exact b1
  · rw [show deriv (deriv fun x => cutStep (Real.log (-x) / c) ^ 2 / 2) t = _ from hH2]; exact b2
end GroundTheory.Heights₂.Heights
