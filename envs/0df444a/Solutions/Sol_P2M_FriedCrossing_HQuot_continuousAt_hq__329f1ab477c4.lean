-- Prove2me | solution 1 for P2M_FriedCrossing_HQuot_continuousAt_hq__329f1ab477c4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:03:26.640429+00:00
-- url     : https://prove2.me/submissions/8ebc33f2-1557-4ee1-a0a6-5b0ec374028f

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Theorems.Thm_FriedCrossing_HQuot_taylor2
import Theorems.Thm_FriedCrossing_Hadamard_entry_slope_eq


set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.HQuot
namespace FriedCrossing.HQuot
theorem _root_.solution {F F' F'' : ℝ → ℝ → ℝ}
    (hF : ∀ θ t, HasDerivAt (F θ) (F' θ t) t) (hF' : ∀ θ t, HasDerivAt (F' θ) (F'' θ t) t)
    (hc : ContinuousAt (fun q : ℝ × ℝ => F'' q.1 q.2) (0, 0)) :
    ContinuousAt (fun p : ℝ × ℝ => hq' (F p.1) (F' p.1) (F'' p.1) p.2) (0, 0) := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp hc (ε / 4) (by positivity)
  refine ⟨δ, hδ, fun p hp => ?_⟩
  obtain ⟨θ, τ⟩ := p
  have hp' : |θ| < δ ∧ |τ| < δ := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, sub_zero, max_lt_iff] at hp
    exact hp
  have hnear : ∀ ξ, |ξ| < δ → |F'' θ ξ - F'' 0 0| < ε / 4 := fun ξ hξ => by
    have := hball (show dist ((θ, ξ) : ℝ × ℝ) (0, 0) < δ by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, sub_zero]; exact max_lt hp'.1 hξ)
    rwa [Real.dist_eq] at this
  have h00 : hq' (F 0) (F' 0) (F'' 0) 0 = F'' 0 0 / 2 := by simp [hq']
  rw [Real.dist_eq, h00]
  by_cases hτ : τ = 0
  · subst hτ
    have h0 : hq' (F θ) (F' θ) (F'' θ) 0 = F'' θ 0 / 2 := by simp [hq']
    rw [h0]
    have := hnear 0 (by simpa using hδ)
    calc |F'' θ 0 / 2 - F'' 0 0 / 2| = |F'' θ 0 - F'' 0 0| / 2 := by
          rw [← sub_div, abs_div, abs_two]
      _ < ε := by linarith
  · have hne : hq' (F θ) (F' θ) (F'' θ) τ = (τ * F' θ τ - (F θ τ - F θ 0)) / τ ^ 2 := by
      simp [hq', hτ]
    rw [hne]
    obtain ⟨ξ, hξ, hR⟩ := taylor2 (hF θ) (hF' θ) hτ
    obtain ⟨η, hη, hslope⟩ := Hadamard.entry_slope_eq (hF' θ) hτ
    have h1 : F' θ τ = F' θ 0 + τ * F'' θ η := by rw [← hslope]; field_simp; ring
    have hF : F θ τ - F θ 0 = τ * F' θ 0 + τ ^ 2 * F'' θ ξ / 2 := by linarith
    have hval : (τ * F' θ τ - (F θ τ - F θ 0)) / τ ^ 2 = F'' θ η - F'' θ ξ / 2 := by
      have hτ2 : τ ^ 2 ≠ 0 := pow_ne_zero 2 hτ
      rw [h1, hF]
      field_simp
      ring
    rw [hval]
    have e1 := hnear η (lt_trans hη hp'.2)
    have e2 := hnear ξ (lt_trans hξ hp'.2)
    calc |F'' θ η - F'' θ ξ / 2 - F'' 0 0 / 2|
        = |(F'' θ η - F'' 0 0) - (F'' θ ξ - F'' 0 0) / 2| := by ring_nf
      _ ≤ |F'' θ η - F'' 0 0| + |(F'' θ ξ - F'' 0 0) / 2| := abs_sub _ _
      _ = |F'' θ η - F'' 0 0| + |F'' θ ξ - F'' 0 0| / 2 := by rw [abs_div, abs_two]
      _ < ε := by linarith
end FriedCrossing.HQuot
