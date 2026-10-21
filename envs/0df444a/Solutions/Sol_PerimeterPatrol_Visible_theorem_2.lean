-- Prove2me | solution 1 for PerimeterPatrol.Visible.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T23:17:39.171177+00:00
-- url     : https://prove2.me/submissions/d3c7a8ad-36ed-414b-a0c7-25fbc13ee9f8

import Mathlib
import Definitions.Def_PerimeterPatrol_Visible_Model
import Definitions.Def_PerimeterPatrol_Visible_OptimalPatrol
import Theorems.Thm_PerimeterPatrol_Visible_optimalPatrol_feasible
import Theorems.Thm_PerimeterPatrol_Visible_optimalPatrol_detection_eq
import Theorems.Thm_PerimeterPatrol_Visible_converse
import Theorems.Thm_PerimeterPatrol_Visible_patrolValue_monotone

open MeasureTheory

open PerimeterPatrol.Visible in
theorem solution (lam t p : ℝ) (hlam : 0 < lam) (ht : 0 < t) (hp0 : 0 < p) (hp1 : p ≤ 1) : IsMixedStrategy lam (optimalPatrol lam t) ∧ (∀ τ : (ℕ → ℝ) → ℝ, IsAttack t τ → patrolValue lam t p ≤ detectionProb p t (optimalPatrol lam t) τ) ∧ (∀ μ : Measure (ℕ → ℝ), IsMixedStrategy lam μ → ∀ ε : ℝ, 0 < ε → ∃ τ : (ℕ → ℝ) → ℝ, IsAttack t τ ∧ detectionProb p t μ τ < patrolValue lam t p + ε) ∧ (MonotoneOn (fun l : ℝ => patrolValue l t p) (Set.Ioi 0) ∧ MonotoneOn (fun u : ℝ => patrolValue lam u p) (Set.Ioi 0) ∧ MonotoneOn (fun q : ℝ => patrolValue lam t q) (Set.Ioc 0 1)) := by
  refine ⟨optimalPatrol_feasible lam t hlam ht, fun τ hτ => ?_, fun μ hμ ε hε => ?_,
    patrolValue_monotone lam t p hlam ht hp0 hp1⟩
  · exact (optimalPatrol_detection_eq lam t p hlam ht hp0 hp1 τ hτ).symm.le
  · obtain ⟨y, hy, h⟩ := converse lam t p hlam ht hp0 hp1 μ hμ ε hε
    refine ⟨fun _ => y, ⟨⟨y, y + t, hy, fun _ => ⟨le_rfl, le_rfl⟩⟩, fun u => ?_⟩, h⟩
    by_cases hu : y ≤ u
    · simp [hu]
    · simp [hu]
