-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_OsgoodSeparate_cauchy_torus_ff70d79abd01
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:32:44.552819+00:00
-- url     : https://prove2.me/submissions/18ab5560-95d5-472d-93cf-41f0c7694a78

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PRiemannExtensionSlices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_OsgoodSeparate_cons_mem_ball_309c0470889e
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_continuous_torusMap
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_differentiable_cons_left
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_differentiable_cons_right
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_mem_ball_pi_iff
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_torusMap_mem_closedBall
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Complex Metric MeasureTheory Set Filter Topology ReciprocityTheory.AnForm.Osgood
  GroundTheory.Heights₂.Heights.Regular.RiemannExtensionSlices
open scoped Real
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.OsgoodSeparate
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.OsgoodSeparate
theorem _root_.solution : ∀ (n : ℕ) (G : (Fin n → ℂ) → ℂ) (c : Fin n → ℂ) (R : ℝ),
    ContinuousOn G (ball c R) →
    (∀ z ∈ ball c R, ∀ i, DifferentiableAt ℂ (fun t => G (Function.update z i t)) (z i)) →
    ∀ r : ℝ, 0 < r → r < R → ∀ z ∈ ball c r,
    (∯ ζ in T(c, fun _ => r), (∏ i, (ζ i - z i)⁻¹) * G ζ) = (2 * π * I) ^ n * G z
  | 0, G, c, _, _, _, r, _, _, z, _ => by
    rw [torusIntegral_dim0]
    simp [Subsingleton.elim z c]
  | n + 1, G, c, R, hc, hs, r, hr0, hrR, z, hz => by
    have htor : ∀ θ, torusMap c (fun _ => r) θ ∈ ball c R := fun θ =>
      closedBall_subset_ball hrR (torusMap_mem_closedBall c hr0.le θ)
    have hint : TorusIntegrable (fun ζ => (∏ i, (ζ i - z i)⁻¹) * G ζ) c (fun _ => r) := by
      refine ContinuousOn.integrableOn_compact isCompact_Icc (Continuous.continuousOn ?_)
      refine Continuous.mul ?_ (hc.comp_continuous (continuous_torusMap c r) htor)
      refine continuous_finsetProd _ fun i _ => Continuous.inv₀ ?_ fun θ => torusMap_sub_ne hr0 hz θ i
      exact ((continuous_apply i).comp (continuous_torusMap c r)).sub continuous_const
    rw [torusIntegral_succ hint]
    have hz' : Fin.tail z ∈ ball (Fin.tail c) r :=
      (mem_ball_pi_iff hr0).mpr fun i => by simpa [Fin.tail] using (mem_ball_pi_iff hr0).mp hz i.succ
    have hz'R : Fin.tail z ∈ ball (Fin.tail c) R := ball_subset_ball hrR.le hz'
    have hz0 : z 0 ∈ ball (c 0) r := (mem_ball_pi_iff hr0).mp hz 0
    have key : EqOn (fun x => ∯ y in T(c ∘ Fin.succ, (fun _ => r) ∘ Fin.succ),
          (∏ i, ((Fin.cons x y : Fin (n + 1) → ℂ) i - z i)⁻¹) * G (Fin.cons x y))
        (fun x => (2 * π * I) ^ n * ((x - z 0)⁻¹ * G (Fin.cons x (Fin.tail z))))
        (sphere (c 0) r) := by
      intro x hx
      have hxR : x ∈ ball (c 0) R := mem_ball.mpr (by rw [mem_sphere.mp hx]; exact hrR)
      have hc' : ContinuousOn (fun y => G (Fin.cons x y)) (ball (Fin.tail c) R) :=
        hc.comp (differentiable_cons_right x).continuous.continuousOn fun y hy => cons_mem_ball hxR hy
      have hs' : ∀ w ∈ ball (Fin.tail c) R, ∀ i : Fin n,
          DifferentiableAt ℂ (fun t => (fun y => G (Fin.cons x y)) (Function.update w i t)) (w i) := by
        intro w hw i
        have h := hs _ (cons_mem_ball hxR hw) i.succ
        simp only [Fin.cons_succ] at h
        simpa only [Fin.cons_update] using h
      have ih := solution n (fun y => G (Fin.cons x y)) (Fin.tail c) R hc' hs' r hr0 hrR
        (Fin.tail z) hz'
      have e0 : c ∘ Fin.succ = Fin.tail c := rfl
      have e1 : ((fun _ : Fin (n + 1) => r) ∘ Fin.succ) = fun _ => r := rfl
      simp only [e0, e1]
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_assoc]
      rw [torusIntegral_const_mul]
      simp only [Fin.tail] at ih
      rw [ih]
      ring
    rw [circleIntegral.integral_congr hr0.le key, circleIntegral.integral_const_mul]
    have hcont : ContinuousOn (fun x => G (Fin.cons x (Fin.tail z))) (closedBall (c 0) r) :=
      hc.comp (differentiable_cons_left (Fin.tail z)).continuous.continuousOn fun x hx =>
        cons_mem_ball (closedBall_subset_ball hrR hx) hz'R
    have hdiff : ∀ x ∈ ball (c 0) r \ (∅ : Set ℂ),
        DifferentiableAt ℂ (fun x => G (Fin.cons x (Fin.tail z))) x := by
      intro x hx
      have h := hs _ (cons_mem_ball (ball_subset_ball hrR.le hx.1) hz'R) 0
      simp only [Fin.cons_zero, Fin.update_cons_zero] at h
      exact h
    have h1 := circleIntegral_sub_inv_smul_of_differentiable_on_off_countable countable_empty
      hz0 hcont hdiff
    simp only [smul_eq_mul] at h1
    rw [h1, Fin.cons_self_tail, pow_succ]
    ring
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.OsgoodSeparate
