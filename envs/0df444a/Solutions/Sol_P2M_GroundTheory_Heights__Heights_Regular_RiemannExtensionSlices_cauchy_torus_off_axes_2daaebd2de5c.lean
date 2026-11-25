-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_cauchy_torus_off_axes_2daaebd2de5c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:16:13.900176+00:00
-- url     : https://prove2.me/submissions/7d98b8b9-d05b-4aa0-ae55-91833a8f8d54

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StRiemannSlices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PRiemannExtensionSlices
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_continuous_comp_torusMap_zero_f772cf319c00
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_cons_mem_ball_one_42c41052423a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_cons_ne_zero_fc6b2140ec32
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_continuous_torusMap
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_differentiable_cons_left
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_differentiable_cons_right
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_mem_ball_pi_iff
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_torusMap_sub_ne


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Complex Metric MeasureTheory Set Filter Topology ReciprocityTheory.AnForm.Osgood
open scoped Real
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.RiemannExtensionSlices
namespace GroundTheory.Heights₂.Heights.Regular.RiemannExtensionSlices
theorem _root_.solution : ∀ (n : ℕ) (G : (Fin n → ℂ) → ℂ),
    (∀ ζ ∈ ball (0 : Fin n → ℂ) 1, (∀ i, ζ i ≠ 0) → DifferentiableAt ℂ G ζ) →
    (∀ z ∈ ball (0 : Fin n → ℂ) 1, ∀ i : Fin n, (∀ j, j ≠ i → z j ≠ 0) →
      ∃ c : ℂ, Tendsto (fun x : ℂ => G (Function.update z i x)) (𝓝[≠] 0) (𝓝 c)) →
    ∀ r : ℝ, 0 < r → r < 1 → ∀ z ∈ ball (0 : Fin n → ℂ) r, (∀ i, z i ≠ 0) →
    (∯ ζ in T(0, fun _ => r), (∏ i, (ζ i - z i)⁻¹) * G ζ) = (2 * π * I) ^ n * G z
  | 0, G, _, _, r, _, _, z, _, _ => by
    rw [torusIntegral_dim0]
    simp [Subsingleton.elim z 0]
  | n + 1, G, hd, hlim, r, hr0, hr1, z, hz, hzW => by
    have hint : TorusIntegrable (fun ζ => (∏ i, (ζ i - z i)⁻¹) * G ζ) 0 (fun _ => r) := by
      refine ContinuousOn.integrableOn_compact isCompact_Icc (Continuous.continuousOn ?_)
      refine Continuous.mul ?_ (continuous_comp_torusMap_zero hd hr0 hr1)
      refine continuous_finsetProd _ fun i _ => Continuous.inv₀ ?_ fun θ => torusMap_sub_ne hr0 hz θ i
      exact ((continuous_apply i).comp (continuous_torusMap 0 r)).sub continuous_const
    rw [torusIntegral_succ hint]
    have hz1 : z ∈ ball (0 : Fin (n + 1) → ℂ) 1 := ball_subset_ball hr1.le hz
    have hz' : Fin.tail z ∈ ball (0 : Fin n → ℂ) r :=
      (mem_ball_pi_iff hr0).mpr fun i => by simpa [Fin.tail] using (mem_ball_pi_iff hr0).mp hz i.succ
    have hz'1 : Fin.tail z ∈ ball (0 : Fin n → ℂ) 1 := ball_subset_ball hr1.le hz'
    have hzW' : ∀ i, Fin.tail z i ≠ 0 := fun i => hzW i.succ
    have key : EqOn (fun x => ∯ y in T((0 : Fin (n + 1) → ℂ) ∘ Fin.succ, (fun _ => r) ∘ Fin.succ),
          (∏ i, ((Fin.cons x y : Fin (n + 1) → ℂ) i - z i)⁻¹) * G (Fin.cons x y))
        (fun x => (2 * π * I) ^ n * ((x - z 0)⁻¹ * G (Fin.cons x (Fin.tail z))))
        (sphere ((0 : Fin (n + 1) → ℂ) 0) r) := by
      intro x hx
      have hxn : ‖x‖ = r := by simpa using hx
      have hx0 : x ≠ 0 := by
        rintro rfl
        rw [norm_zero] at hxn
        exact hr0.ne hxn
      have hx1 : ‖x‖ < 1 := hxn ▸ hr1
      have hd' : ∀ ζ ∈ ball (0 : Fin n → ℂ) 1, (∀ i, ζ i ≠ 0) →
          DifferentiableAt ℂ (fun y => G (Fin.cons x y)) ζ := fun ζ hζ hζW =>
        (hd _ (cons_mem_ball_one hx1 hζ) (cons_ne_zero hx0 hζW)).comp ζ (differentiable_cons_right x ζ)
      have hlim' : ∀ w ∈ ball (0 : Fin n → ℂ) 1, ∀ i : Fin n, (∀ j, j ≠ i → w j ≠ 0) →
          ∃ c : ℂ, Tendsto (fun t : ℂ => (fun y => G (Fin.cons x y)) (Function.update w i t))
            (𝓝[≠] 0) (𝓝 c) := by
        intro w hw i hwi
        have hne : ∀ j, j ≠ i.succ → (Fin.cons x w : Fin (n + 1) → ℂ) j ≠ 0 := by
          intro j hj
          induction j using Fin.cases with
          | zero => simpa using hx0
          | succ k => simpa using hwi k (fun h => hj (by rw [h]))
        obtain ⟨c, hc⟩ := hlim _ (cons_mem_ball_one hx1 hw) i.succ hne
        refine ⟨c, ?_⟩
        simp only [Fin.cons_update]
        exact hc
      have ih := solution n (fun y => G (Fin.cons x y)) hd' hlim' r hr0 hr1 (Fin.tail z) hz' hzW'
      have e0 : ((0 : Fin (n + 1) → ℂ) ∘ Fin.succ) = 0 := rfl
      have e1 : ((fun _ : Fin (n + 1) => r) ∘ Fin.succ) = fun _ => r := rfl
      simp only [e0, e1]
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_assoc]
      rw [torusIntegral_const_mul]
      simp only [Fin.tail] at ih
      rw [ih]
      ring
    rw [circleIntegral.integral_congr hr0.le key, circleIntegral.integral_const_mul]
    obtain ⟨c, hc⟩ := hlim z hz1 0 (fun j _ => hzW j)
    have hupd : ∀ x : ℂ, Function.update z 0 x = Fin.cons x (Fin.tail z) := fun x => by
      rw [← Fin.update_cons_zero (x := z 0) (p := Fin.tail z) (z := x), Fin.cons_self_tail]
    have hg : Tendsto (fun x => G (Fin.cons x (Fin.tail z))) (𝓝[≠] 0) (𝓝 c) := by
      simpa only [hupd] using hc
    have hgd : ∀ x : ℂ, x ≠ 0 → ‖x‖ < 1 → DifferentiableAt ℂ (fun x => G (Fin.cons x (Fin.tail z))) x :=
      fun x hx0 hx1 => (hd _ (cons_mem_ball_one hx1 hz'1) (cons_ne_zero hx0 hzW')).comp x
        (differentiable_cons_left (Fin.tail z) x)
    have heq : ∀ x : ℂ, x ≠ 0 → Function.update (fun x => G (Fin.cons x (Fin.tail z))) 0 c =ᶠ[𝓝 x]
        (fun x => G (Fin.cons x (Fin.tail z))) := fun x hx =>
      Filter.eventually_of_mem (isOpen_ne.mem_nhds hx) fun y hy => Function.update_of_ne hy _ _
    have hcont : ContinuousOn (Function.update (fun x => G (Fin.cons x (Fin.tail z))) 0 c)
        (closedBall 0 r) := by
      intro x hx
      by_cases hx0 : x = 0
      · subst hx0
        exact (continuousAt_update_same.mpr hg).continuousWithinAt
      · have hx1 : ‖x‖ < 1 := lt_of_le_of_lt (mem_closedBall_zero_iff.mp hx) hr1
        exact ((hgd x hx0 hx1).continuousAt.congr (heq x hx0).symm).continuousWithinAt
    have hdiff : ∀ x ∈ ball (0 : ℂ) r \ {0},
        DifferentiableAt ℂ (Function.update (fun x => G (Fin.cons x (Fin.tail z))) 0 c) x :=
      fun x hx => (hgd x hx.2 (lt_trans (mem_ball_zero_iff.mp hx.1) hr1)).congr_of_eventuallyEq
        (heq x hx.2)
    have hz0 : z 0 ∈ ball (0 : ℂ) r := by simpa using (mem_ball_pi_iff hr0).mp hz 0
    have h1 := circleIntegral_sub_inv_smul_of_differentiable_on_off_countable (countable_singleton 0)
      hz0 hcont hdiff
    simp only [smul_eq_mul] at h1
    have hcirc : (∮ x in C((0 : Fin (n + 1) → ℂ) 0, r), (x - z 0)⁻¹ * G (Fin.cons x (Fin.tail z))) =
        ∮ x in C(0, r), (x - z 0)⁻¹ *
          Function.update (fun x => G (Fin.cons x (Fin.tail z))) 0 c x := by
      refine circleIntegral.integral_congr hr0.le fun x hx => ?_
      have hxn : ‖x‖ = r := by simpa using hx
      have hx0 : x ≠ 0 := by
        rintro rfl
        rw [norm_zero] at hxn
        exact hr0.ne hxn
      simp only [Function.update_of_ne hx0]
    rw [hcirc, h1, Function.update_of_ne (hzW 0), Fin.cons_self_tail, pow_succ]
    ring
end GroundTheory.Heights₂.Heights.Regular.RiemannExtensionSlices
