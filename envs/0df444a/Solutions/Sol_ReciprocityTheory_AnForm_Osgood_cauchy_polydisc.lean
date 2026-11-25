-- Prove2me | solution 1 for ReciprocityTheory.AnForm.Osgood.cauchy_polydisc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:14:10.953242+00:00
-- url     : https://prove2.me/submissions/a9cba4ed-0884-40e9-bb1d-656fcd93c5b8

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_OsgoodA
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_differentiable_cons_right
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_differentiable_cons_left
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_mem_closedBall_pi_iff
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_mem_ball_pi_iff
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_torusIntegrable_kernel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.Osgood
open Complex Metric MeasureTheory Set Filter Topology
open scoped Real
namespace ReciprocityTheory.AnForm.Osgood
theorem _root_.solution : ∀ (n : ℕ) (f : (Fin n → ℂ) → ℂ) (c : Fin n → ℂ) (r : ℝ), 0 < r →
    (∀ ζ ∈ closedBall c r, DifferentiableAt ℂ f ζ) → ∀ z ∈ ball c r,
    (∯ ζ in T(c, fun _ => r), (∏ i, (ζ i - z i)⁻¹) * f ζ) = (2 * π * I) ^ n * f z
  | 0, f, c, r, _, _, z, _ => by
    rw [torusIntegral_dim0]
    simp [Subsingleton.elim z c]
  | n + 1, f, c, r, hr, hf, z, hz => by
    rw [torusIntegral_succ (torusIntegrable_kernel hr hf hz)]
    have hz0 : z 0 ∈ ball (c 0) r := (mem_ball_pi_iff hr).mp hz 0
    have hz' : Fin.tail z ∈ ball (fun i => c (Fin.succ i)) r :=
      (mem_ball_pi_iff hr).mpr fun i => (mem_ball_pi_iff hr).mp hz i.succ
    have hcons : ∀ x ∈ closedBall (c 0) r, ∀ y ∈ closedBall (fun i => c (Fin.succ i)) r,
        (Fin.cons x y : Fin (n + 1) → ℂ) ∈ closedBall c r := by
      intro x hx y hy
      refine (mem_closedBall_pi_iff hr.le).mpr fun i => ?_
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hx
      · simpa using (mem_closedBall_pi_iff hr.le).mp hy j
    have key : EqOn (fun x => ∯ y in T(c ∘ Fin.succ, (fun _ => r) ∘ Fin.succ),
          (∏ i, ((Fin.cons x y : Fin (n + 1) → ℂ) i - z i)⁻¹) * f (Fin.cons x y))
        (fun x => (2 * π * I) ^ n * ((x - z 0)⁻¹ * f (Fin.cons x (Fin.tail z)))) (sphere (c 0) r) := by
      intro x hx
      have hxc : x ∈ closedBall (c 0) r := sphere_subset_closedBall hx
      have ih := solution n (fun y => f (Fin.cons x y)) (fun i => c (Fin.succ i)) r hr
        (fun ζ hζ => (hf _ (hcons x hxc ζ hζ)).comp ζ (differentiable_cons_right x ζ)) (Fin.tail z) hz'
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Function.comp_def, mul_assoc]
      rw [torusIntegral_const_mul]
      simp only [Fin.tail] at ih
      rw [ih]
      ring
    rw [circleIntegral.integral_congr hr.le key, circleIntegral.integral_const_mul]
    have hd : DifferentiableOn ℂ (fun x => f (Fin.cons x (Fin.tail z))) (closedBall (c 0) r) :=
      fun x hx => ((hf _ (hcons x hx _ (ball_subset_closedBall hz'))).comp x
        (differentiable_cons_left (Fin.tail z) x)).differentiableWithinAt
    have h1 := hd.circleIntegral_sub_inv_smul hz0
    simp only [smul_eq_mul] at h1
    rw [h1, Fin.cons_self_tail, pow_succ]
    ring
end ReciprocityTheory.AnForm.Osgood
