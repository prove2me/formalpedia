-- Prove2me | solution 2 for SpherePacking.finite_center_ball_intersection_set
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:12:18.941545+00:00
-- url     : https://prove2.me/submissions/f1303b88-15f4-4c6a-8e27-40e028fa5097

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
open scoped Pointwise Topology
variable {d : ℕ}
open SpherePacking
open Filter
variable {d : ℕ}


theorem solution (S : SpherePacking d) (R : ℝ) :
    (S.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R).Finite := by
  have hTB : TotallyBounded (S.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R) :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) R).totallyBounded.subset
      (Set.inter_subset_right.trans ball_subset_closedBall)
  have hsep := S.separation_pos
  obtain ⟨t, htfin, hcover⟩ := Metric.totallyBounded_iff.mp hTB (S.separation / 2) (by linarith)
  have hex : ∀ x : ↥(S.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R),
      ∃ y : ↥t, (x : EuclideanSpace ℝ (Fin d)) ∈ ball (y : EuclideanSpace ℝ (Fin d)) (S.separation / 2) := by
    intro x
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hcover x.2)
    exact ⟨⟨y, hy⟩, hxy⟩
  choose g hg using hex
  haveI := htfin.to_subtype
  apply Set.finite_coe_iff.mp
  refine Finite.of_injective g ?_
  intro a b hab
  by_contra hne
  have h1 := S.distinct_centers_separation_bound a b a.2.1 b.2.1 (fun h => hne (Subtype.ext h))
  have ha := hg a
  have hb := hg b
  rw [hab] at ha
  rw [Metric.mem_ball] at ha hb
  have := dist_triangle_right (a : EuclideanSpace ℝ (Fin d)) b (g b)
  linarith

