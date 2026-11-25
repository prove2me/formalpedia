-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticOnNhd_of_continuousOn_of_separately_ff52795ca853
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:17:05.619577+00:00
-- url     : https://prove2.me/submissions/d8b04520-16c6-40b5-a84d-fd5b2d8d35b6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PRiemannExtensionSlices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_OsgoodSeparate_cauchy_torus_ff70d79abd01
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_fctl_kern_3e5189bc629a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_kern_analyticAt_of_mem_f25be706a099
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_continuous_torusMap
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_torusMap_mem_closedBall


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
open OsgoodSeparate
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {n : ℕ} {U : Set (Fin n → ℂ)}
    {g : (Fin n → ℂ) → ℂ} (hU : IsOpen U) (hc : ContinuousOn g U)
    (hs : ∀ z ∈ U, ∀ i, DifferentiableAt ℂ (fun t => g (Function.update z i t)) (z i)) :
    AnalyticOnNhd ℂ g U := by
  intro c hcU
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU c hcU
  have hr : 0 < ε / 2 := half_pos hε
  have hrε : ε / 2 < ε := half_lt_self hε
  have hcb : ContinuousOn g (ball c ε) := hc.mono hball
  have hsb : ∀ z ∈ ball c ε, ∀ i, DifferentiableAt ℂ (fun t => g (Function.update z i t)) (z i) :=
    fun z hz => hs z (hball hz)
  have htor : Continuous fun θ => g (torusMap c (fun _ => ε / 2) θ) :=
    hcb.comp_continuous (continuous_torusMap c _) fun θ =>
      closedBall_subset_ball hrε (torusMap_mem_closedBall c hr.le θ)
  set L := torusFunctional c (ε / 2) g htor
  have hne : (2 * π * I : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by simp [Real.pi_ne_zero, I_ne_zero])
  have han : AnalyticAt ℂ (fun z => ((2 * π * I : ℂ) ^ n)⁻¹ * L (kern c (ε / 2) z)) c :=
    analyticAt_const.mul ((L.analyticAt _).comp (kern_analyticAt_of_mem c hr (mem_ball_self hr)))
  refine han.congr ?_
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with z hz
  show ((2 * π * I : ℂ) ^ n)⁻¹ * fctl c (ε / 2) g (kern c (ε / 2) z) = g z
  rw [fctl_kern hr g hz, cauchy_torus n g c ε hcb hsb (ε / 2) hr hrε z hz, ← mul_assoc,
    inv_mul_cancel₀ hne, one_mul]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
