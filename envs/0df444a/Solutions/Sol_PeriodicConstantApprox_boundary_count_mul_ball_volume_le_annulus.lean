-- Prove2me | solution 1 for PeriodicConstantApprox.boundary_count_mul_ball_volume_le_annulus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/631e148b-8046-4aa6-ad40-79ae0a28c321

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_PeriodicConstantApprox_boundary_half_ball_subset_outer_annulus

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
open scoped Pointwise Topology
variable {d : ℕ}
open PeriodicConstantApprox
open scoped ENNReal Pointwise BigOperators
variable (S : SpherePacking d)
namespace PeriodicConstantApprox
theorem _root_.solution {L : ℝ} (hL : 0 < L)
    (hSsep : S.separation = 1)
    {g : axisCellLattice (d := d) L hL} {s : Finset (EuclideanSpace ℝ (Fin d))}
    (hs_centers : ∀ x ∈ s, x ∈ S.centers)
    (hs_boundary : ∀ x ∈ s,
      x ∈ (g +ᵥ axisAlignedCell (d := d) L) \ (g +ᵥ insetAxisAlignedCell (d := d) L (1 / 2))) :
    (s.card : ℝ≥0∞) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (2⁻¹ : ℝ)) ≤
      volume (((constantCoordinateVector (d := d) (- (1 / 2 : ℝ))) +ᵥ insetAxisAlignedCell (d := d) (L + 1) 0) \
        insetAxisAlignedCell (d := d) L 1) := by
  classical
  let v : EuclideanSpace ℝ (Fin d) := g
  have hdisj :
      Set.PairwiseDisjoint (↑s : Set (EuclideanSpace ℝ (Fin d)))
        (fun x : EuclideanSpace ℝ (Fin d) => ball (x - v) (1 / 2 : ℝ)) := by
    intro x hx y hy hxy
    apply ball_disjoint_ball
    have hdist :=
      S.distinct_centers_separation_bound x y (hs_centers x hx) (hs_centers y hy) hxy
    rw [hSsep] at hdist
    convert hdist using 1 <;> norm_num [dist_eq_norm, sub_sub_sub_cancel_right]
  have hmeas :
      ∀ x ∈ s, MeasurableSet (ball (x - v) (1 / 2 : ℝ)) := by
    intro x hx
    exact measurableSet_ball
  have hvol_union :
      volume (⋃ x ∈ s, ball (x - v) (1 / 2 : ℝ)) =
        ∑ x ∈ s, volume (ball (x - v) (1 / 2 : ℝ)) :=
    measure_biUnion_finset (μ := volume) hdisj hmeas
  have hsub :
      (⋃ x ∈ s, ball (x - v) (1 / 2 : ℝ)) ⊆
        ((constantCoordinateVector (d := d) (-(1 / 2 : ℝ))) +ᵥ
          insetAxisAlignedCell (d := d) (L + 1) 0) \
          insetAxisAlignedCell (d := d) L 1 := by
    intro y hy
    rcases Set.mem_iUnion₂.mp hy with ⟨x, hx, hy⟩
    apply boundary_half_ball_subset_outer_annulus (d := d) L
    refine Set.mem_add.mpr ⟨x - v, ?_, y - (x - v), ?_, ?_⟩
    · have hboundary := hs_boundary x hx
      constructor
      · have hcell := hboundary.1
        simpa [v, Set.mem_vadd_set_iff_neg_vadd_mem, Submodule.vadd_def,
          vadd_eq_add, sub_eq_add_neg, add_comm] using hcell
      · intro hinset
        apply hboundary.2
        simpa [v, Set.mem_vadd_set_iff_neg_vadd_mem, Submodule.vadd_def,
          vadd_eq_add, sub_eq_add_neg, add_comm] using hinset
    · simpa [mem_ball, dist_eq_norm] using hy
    · abel
  calc
    (s.card : ℝ≥0∞) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (2⁻¹ : ℝ)) =
        volume (⋃ x ∈ s, ball (x - v) (1 / 2 : ℝ)) := by
      rw [hvol_union]
      simp [Measure.addHaar_ball_center]
    _ ≤ volume (((constantCoordinateVector (d := d) (-(1 / 2 : ℝ))) +ᵥ
          insetAxisAlignedCell (d := d) (L + 1) 0) \
          insetAxisAlignedCell (d := d) L 1) :=
      volume.mono hsub
end PeriodicConstantApprox
