-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_BrouwerFixedPoint_smooth_of_changeOfVariablesDegree_1b6ab2a0e304
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:33.943578+00:00
-- url     : https://prove2.me/submissions/be8d9e69-8f7b-4516-96f4-363c45baad17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBrouwerFixedPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChangeOfVariablesDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PBrouwerFixedPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open scoped ContDiff
open Metric
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace BrouwerFixedPoint
theorem _root_.solution
    (hL : ChangeOfVariablesDegree.Statement) (n : ℕ) (g : (Fin n → ℝ) → Fin n → ℝ)
    (hg : ContDiff ℝ ∞ g) (hgb : ∀ x, ‖g x‖ ≤ 1) : ∃ x, g x = x := by
  by_contra hne
  push Not at hne
  have hcont : ContinuousOn (fun x => ‖x - g x‖) (closedBall (0 : Fin n → ℝ) 2) :=
    (continuous_id.sub hg.continuous).norm.continuousOn
  obtain ⟨x₀, -, hmin⟩ := (isCompact_closedBall (0 : Fin n → ℝ) 2).exists_isMinOn
    (nonempty_closedBall.2 zero_le_two) hcont
  have hε : 0 < ‖x₀ - g x₀‖ := norm_pos_iff.2 (sub_ne_zero.2 (hne x₀).symm)
  set δ := min ‖x₀ - g x₀‖ 1 with hδ_def
  have hδ : 0 < δ := lt_min hε one_pos

  let χ : ContDiffBump (0 : Fin n → ℝ) := ⟨2, 3, two_pos, by norm_num⟩
  let φ : (Fin n → ℝ) → Fin n → ℝ := fun x => x - χ x • g x
  have hφ : ContDiff ℝ ∞ φ := contDiff_id.sub (χ.contDiff.smul hg)
  have hφc : HasCompactSupport (fun x => φ x - x) := by
    have h : (fun x => φ x - x) = -((fun x => χ x) • g) := by
      funext x; simp [φ]
    rw [h]
    exact χ.hasCompactSupport.smul_right.neg
  have hφδ : ∀ x, δ ≤ ‖φ x‖ := by
    intro x
    by_cases hx : ‖x‖ ≤ 2
    · have hχ : χ x = 1 := χ.one_of_mem_closedBall (mem_closedBall_zero_iff.2 hx)
      have h2 : ‖x₀ - g x₀‖ ≤ ‖x - g x‖ :=
        isMinOn_iff.1 hmin x (mem_closedBall_zero_iff.2 hx)
      simp only [φ, hχ, one_smul]
      exact (min_le_left _ _).trans h2
    · push Not at hx
      have h1 : ‖χ x • g x‖ ≤ 1 := by
        rw [norm_smul, Real.norm_of_nonneg χ.nonneg]
        exact mul_le_one₀ χ.le_one (norm_nonneg _) (hgb x)
      have h3 : ‖x‖ - ‖χ x • g x‖ ≤ ‖φ x‖ := norm_sub_norm_le _ _
      have h4 : δ ≤ 1 := min_le_right _ _
      linarith

  let ψ : ContDiffBump (0 : Fin n → ℝ) := ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  have hzero : ∀ x, ψ (φ x) = 0 := by
    intro x
    by_contra h
    have hmem : φ x ∈ ball (0 : Fin n → ℝ) δ := by
      rw [← ψ.support_eq]; exact h
    rw [mem_ball_zero_iff] at hmem
    exact absurd (hφδ x) (not_le.2 hmem)
  have hL' := hL n φ hφ hφc ψ ψ.contDiff ψ.hasCompactSupport
  simp only [hzero, zero_mul, MeasureTheory.integral_zero] at hL'
  exact (ψ.integral_pos (μ := MeasureTheory.volume)).ne hL'
end BrouwerFixedPoint
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
