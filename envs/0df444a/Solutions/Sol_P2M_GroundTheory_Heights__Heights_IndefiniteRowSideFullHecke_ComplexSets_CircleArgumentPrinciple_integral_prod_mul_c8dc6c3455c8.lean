-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CircleArgumentPrinciple_integral_prod_mul_c8dc6c3455c8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:08:18.718565+00:00
-- url     : https://prove2.me/submissions/7cf55543-d222-4c5e-9200-df23280efb25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCircleArgumentPrinciple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCircleArgumentPrinciple
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CircleArgumentPrinciple_differentiable_prod_sub_b3eb9e92dd8f

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
open Topology Filter Metric Complex Real
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace CircleArgumentPrinciple
theorem _root_.solution {O : Set ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r) (hO : IsOpen O)
    (hball : closedBall c r ⊆ O) {u φ : ℂ → ℂ} (hu : DifferentiableOn ℂ u O)
    (hu0 : ∀ s ∈ closedBall c r, u s ≠ 0) (hφ : DifferentiableOn ℂ φ O) (Z : Multiset ℂ)
    (hZ : ∀ a ∈ Z, a ∈ ball c r) :
    (2 * π * I)⁻¹ * (∮ s in C(c, r), φ s * deriv (fun s => (Z.map fun a => s - a).prod * u s) s /
      ((Z.map fun a => s - a).prod * u s)) = (Z.map φ).sum := by
  induction Z using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero, one_mul, Multiset.sum_zero]
    have hd : ∀ z ∈ closedBall c r, DifferentiableAt ℂ (fun s => φ s * deriv u s / u s) z := by
      intro z hz
      have hzO : O ∈ 𝓝 z := hO.mem_nhds (hball hz)
      exact ((hφ.differentiableAt hzO).mul ((hu.deriv hO).differentiableAt hzO)).div
        (hu.differentiableAt hzO) (hu0 z hz)
    rw [circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le Set.countable_empty
      (fun z hz => (hd z hz).continuousAt.continuousWithinAt)
      (fun z hz => hd z (ball_subset_closedBall hz.1)), mul_zero]
  | cons a Z ih =>
    have hZ' : ∀ b ∈ Z, b ∈ ball c r := fun b hb => hZ b (Multiset.mem_cons_of_mem hb)
    have ha : a ∈ ball c r := hZ a (Multiset.mem_cons_self a Z)
    set F : ℂ → ℂ := fun s => (Z.map fun b => s - b).prod * u s with hFdef
    have hF : DifferentiableOn ℂ F O :=
      ((CircleArgumentPrinciple.differentiable_prod_sub Z).differentiableOn).mul hu

    have hne : ∀ s ∈ sphere c r, ∀ b ∈ a ::ₘ Z, s - b ≠ 0 := by
      intro s hs b hb h0
      have hb' := hZ b hb
      obtain rfl := sub_eq_zero.1 h0
      rw [mem_ball] at hb'
      rw [mem_sphere] at hs
      linarith
    have hFne : ∀ s ∈ sphere c r, F s ≠ 0 := by
      intro s hs
      refine mul_ne_zero (Multiset.prod_ne_zero ?_) (hu0 s (sphere_subset_closedBall hs))
      simp only [Multiset.mem_map, not_exists, not_and]
      exact fun b hb h0 => hne s hs b (Multiset.mem_cons_of_mem hb) h0
    have hsplit : Set.EqOn
        (fun s => φ s * deriv (fun s => ((a ::ₘ Z).map fun b => s - b).prod * u s) s /
          (((a ::ₘ Z).map fun b => s - b).prod * u s))
        (fun s => (s - a)⁻¹ • φ s + φ s * deriv F s / F s) (sphere c r) := by
      intro s hs
      have hsO : O ∈ 𝓝 s := hO.mem_nhds (hball (sphere_subset_closedBall hs))
      have hfun : (fun s => ((a ::ₘ Z).map fun b => s - b).prod * u s) = fun s => (s - a) * F s := by
        funext w
        simp only [Multiset.map_cons, Multiset.prod_cons, hFdef, mul_assoc]
      have hval : ((a ::ₘ Z).map fun b => s - b).prod * u s = (s - a) * F s := by
        simp only [Multiset.map_cons, Multiset.prod_cons, hFdef, mul_assoc]
      have hder : deriv (fun s => (s - a) * F s) s = 1 * F s + (s - a) * deriv F s :=
        (((hasDerivAt_id' s).sub_const a).mul (hF.differentiableAt hsO).hasDerivAt).deriv
      have hsa : s - a ≠ 0 := hne s hs a (Multiset.mem_cons_self a Z)
      have hFs := hFne s hs
      show φ s * deriv (fun s => ((a ::ₘ Z).map fun b => s - b).prod * u s) s /
          (((a ::ₘ Z).map fun b => s - b).prod * u s) = (s - a)⁻¹ • φ s + φ s * deriv F s / F s
      rw [hfun, hder, hval, smul_eq_mul]
      field_simp
    have hint1 : CircleIntegrable (fun s => (s - a)⁻¹ • φ s) c r := by
      refine ContinuousOn.circleIntegrable hr.le ?_
      simp only [smul_eq_mul]
      refine ContinuousOn.mul ?_ (hφ.continuousOn.mono (sphere_subset_closedBall.trans hball))
      exact (continuousOn_id.sub continuousOn_const).inv₀
        (fun s hs => hne s hs a (Multiset.mem_cons_self a Z))
    have hint2 : CircleIntegrable (fun s => φ s * deriv F s / F s) c r := by
      refine ContinuousOn.circleIntegrable hr.le ?_
      intro s hs
      have hsO : O ∈ 𝓝 s := hO.mem_nhds (hball (sphere_subset_closedBall hs))
      exact (((hφ.differentiableAt hsO).mul ((hF.deriv hO).differentiableAt hsO)).div
        (hF.differentiableAt hsO) (hFne s hs)).continuousAt.continuousWithinAt
    have hcauchy : (2 * π * I : ℂ)⁻¹ • (∮ s in C(c, r), (s - a)⁻¹ • φ s) = φ a :=
      two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
        Set.countable_empty ha (hφ.continuousOn.mono hball)
        (fun z hz => hφ.differentiableAt (hO.mem_nhds (hball (ball_subset_closedBall hz.1))))
    rw [circleIntegral.integral_congr hr.le hsplit, circleIntegral.integral_add hint1 hint2, mul_add,
      ← smul_eq_mul, hcauchy, ih hZ', Multiset.map_cons, Multiset.sum_cons]
end CircleArgumentPrinciple
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
