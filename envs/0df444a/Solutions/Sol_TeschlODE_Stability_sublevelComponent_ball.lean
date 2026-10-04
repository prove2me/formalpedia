-- Prove2me | solution 1 for TeschlODE.Stability.sublevelComponent_ball
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T07:00:31.736163+00:00
-- url     : https://prove2.me/submissions/0223618a-30e4-4ebc-9ad2-cefc8ea3e152

import Mathlib
import Definitions.Def_TeschlODE_Stability_IsIntegralCurve
import Definitions.Def_TeschlODE_Stability_IsLiapunovFunction
import Definitions.Def_TeschlODE_Stability_sublevelComponent

set_option autoImplicit false

open TeschlODE.Stability in
theorem solution {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n))) (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ M) (hfix : f x₀ = 0)
    (U : Set (EuclideanSpace ℝ (Fin n))) (L : EuclideanSpace ℝ (Fin n) → ℝ)
    (hL : IsLiapunovFunction f M x₀ U L) :
    ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧
      sublevelComponent U L x₀ ε ⊆ Metric.ball x₀ δ ∧
      Metric.ball x₀ ε ⊆ sublevelComponent U L x₀ δ := by
  intro δ hδ
  obtain ⟨hU, hx₀U, -, hLc, hL0, hpos, -⟩ := hL
  obtain ⟨r0, hr0, hr0U⟩ := Metric.isOpen_iff.mp hU x₀ hx₀U
  set r : ℝ := min (r0 / 2) δ with hr_def
  have hr : 0 < r := lt_min (by linarith) hδ
  have hrδ : r ≤ δ := min_le_right _ _
  have hrU : Metric.closedBall x₀ r ⊆ U := by
    intro y hy
    apply hr0U
    rw [Metric.mem_closedBall] at hy
    rw [Metric.mem_ball]
    have : r ≤ r0 / 2 := min_le_left _ _
    linarith
  have hK : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ y ∈ Metric.sphere x₀ r, ε₁ < L y := by
    rcases (Metric.sphere x₀ r).eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · obtain ⟨y0, hy0, hmin⟩ := (isCompact_sphere x₀ r).exists_isMinOn h
        (hLc.mono (Metric.sphere_subset_closedBall.trans hrU))
      have hy0ne : y0 ≠ x₀ := by
        intro e
        rw [e, Metric.mem_sphere, dist_self] at hy0
        linarith
      have hLy0 : 0 < L y0 := hpos y0 (hrU (Metric.sphere_subset_closedBall hy0)) hy0ne
      refine ⟨L y0 / 2, by positivity, fun y hy => ?_⟩
      have : L y0 ≤ L y := hmin hy
      linarith
  obtain ⟨ε₁, hε₁, hK⟩ := hK
  have hcont : ContinuousAt L x₀ := hLc.continuousAt (hU.mem_nhds hx₀U)
  obtain ⟨ε₂, hε₂, hball⟩ := Metric.continuousAt_iff.mp hcont δ hδ
  refine ⟨min ε₁ (min ε₂ r), lt_min hε₁ (lt_min hε₂ hr), ?_, ?_⟩
  · have hsub : sublevelComponent U L x₀ (min ε₁ (min ε₂ r)) ⊆ Metric.ball x₀ r := by
      unfold sublevelComponent
      refine isPreconnected_connectedComponentIn.subset_left_of_subset_union
        Metric.isOpen_ball (show IsClosed (Metric.closedBall x₀ r) from Metric.isClosed_closedBall).isOpen_compl
        ?_ ?_ ?_
      · rw [Set.disjoint_compl_right_iff_subset]
        exact Metric.ball_subset_closedBall
      · intro z hz
        have hzF := connectedComponentIn_subset _ _ hz
        obtain ⟨hzU, hzL⟩ := hzF
        rcases lt_trichotomy (dist z x₀) r with h | h | h
        · left; exact h
        · exfalso
          have := hK z (by rw [Metric.mem_sphere]; exact h)
          have : min ε₁ (min ε₂ r) ≤ ε₁ := min_le_left _ _
          linarith
        · right
          rw [Set.mem_compl_iff, Metric.mem_closedBall, not_le]
          exact h
      · refine ⟨x₀, mem_connectedComponentIn ?_, Metric.mem_ball_self hr⟩
        refine ⟨hx₀U, ?_⟩
        rw [hL0]
        exact le_of_lt (lt_min hε₁ (lt_min hε₂ hr))
    exact fun y hy => Metric.ball_subset_ball hrδ (hsub hy)
  · unfold sublevelComponent
    refine (convex_ball x₀ _).isPreconnected.subset_connectedComponentIn
      (Metric.mem_ball_self (lt_min hε₁ (lt_min hε₂ hr))) ?_
    intro z hz
    rw [Metric.mem_ball] at hz
    have hz2 : dist z x₀ < ε₂ := lt_of_lt_of_le hz ((min_le_right _ _).trans (min_le_left _ _))
    have hz3 : dist z x₀ < r := lt_of_lt_of_le hz ((min_le_right _ _).trans (min_le_right _ _))
    refine ⟨hrU (Metric.mem_closedBall.mpr hz3.le), ?_⟩
    have := hball hz2
    rw [Real.dist_eq, hL0, sub_zero] at this
    exact le_of_lt (lt_of_le_of_lt (le_abs_self _) this)
