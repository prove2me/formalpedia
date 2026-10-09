-- Prove2me | solution 1 for RayBundle.MetricSegment.four_point_thin
-- status  : ACCEPTED   (prove)
-- author  : @jawneeboy
-- created : 2026-10-08T19:38:29.961992+00:00
-- url     : https://prove2.me/submissions/aafa3ead-a83c-4729-bb66-d9f03690a9d4

import Definitions.Def_RayBundle_MetricPathGeometry
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Isometry

-- Source: RayBundle.Thm_Cayley_MetricSegment_dist_finish
namespace RayBundle

theorem MetricSegment.dist_finish {X : Type*} [MetricSpace X] {a b : X}
    (c : MetricSegment a b) (t : Set.Icc (0 : ℝ) (dist a b)) :
    dist (c.map t) b = dist a b - t.val := by
  calc
    dist (c.map t) b = dist (c.map t) (c.map ⟨dist a b, ⟨dist_nonneg, le_rfl⟩⟩) :=
      congrArg (dist (c.map t)) c.finish.symm
    _ = dist t (⟨dist a b, ⟨dist_nonneg, le_rfl⟩⟩ : Set.Icc (0 : ℝ) (dist a b)) := c.isometry.dist_eq _ _
    _ = dist a b - t.val := by
      change |t.val - dist a b| = dist a b - t.val
      rw [abs_of_nonpos (sub_nonpos.mpr t.property.2)]
      ring

end RayBundle

-- Source: RayBundle.Thm_Cayley_MetricSegment_dist_start
namespace RayBundle

theorem MetricSegment.dist_start {X : Type*} [MetricSpace X] {a b : X}
    (c : MetricSegment a b) (t : Set.Icc (0 : ℝ) (dist a b)) : dist a (c.map t) = t.val := by
  calc
    dist a (c.map t) = dist (c.map ⟨0, ⟨le_rfl, dist_nonneg⟩⟩) (c.map t) :=
      congrArg (fun p => dist p (c.map t)) c.start.symm
    _ = dist (⟨0, ⟨le_rfl, dist_nonneg⟩⟩ : Set.Icc (0 : ℝ) (dist a b)) t := c.isometry.dist_eq _ _
    _ = t.val := by
      change |0 - t.val| = t.val
      simp [abs_of_nonneg t.property.1]

end RayBundle

-- Source: RayBundle.Thm_Cayley_four_point_close_on_side
namespace RayBundle

/-- Two applications of the four-point inequality compare corresponding triangle-side points. -/
theorem four_point_close_on_side {X : Type*} [MetricSpace X] (K : ℝ) (hK : 0 ≤ K)
    (hfour : ∀ a b c d : X, dist a b + dist c d ≤
      max (dist a c + dist b d) (dist a d + dist b c) + K)
    {a b c p q : X} (hp : dist a p + dist p b = dist a b)
    (hbranch : 2 * dist a p ≤ dist a b + dist a c - dist b c)
    (hq : dist a q = dist a p) (hqc : dist q c = dist a c - dist a p) :
    dist p q ≤ 2 * K := by
  have h1 := hfour a b c p
  rw [dist_comm b p] at h1
  have hdom : dist a p + dist b c ≤ dist a c + dist p b := by linarith
  rw [max_eq_left hdom] at h1
  have hcp : dist c p ≤ dist a c - dist a p + K := by linarith
  have h2 := hfour a c p q
  rw [hq, dist_comm c q, hqc] at h2
  have hmax : max (dist a p + (dist a c - dist a p))
      (dist a p + dist c p) ≤ dist a c + K := by
    apply max_le <;> linarith
  linarith

end RayBundle

-- Source: RayBundle.Thm_Cayley_MetricSegment_four_point_thin
namespace RayBundle

end RayBundle

open RayBundle
universe u
/-- The four-point inequality makes all continuous geodesic triangles uniformly thin. -/
theorem solution {X : Type*} [MetricSpace X] (K : ℝ) (hK : 0 ≤ K)
    (hfour : ∀ a b c d : X, dist a b + dist c d ≤
      max (dist a c + dist b d) (dist a d + dist b c) + K)
    {a b c : X} (ab : RayBundle.MetricSegment a b) (ac : RayBundle.MetricSegment a c) (bc : RayBundle.MetricSegment b c)
    (t : Set.Icc (0 : ℝ) (dist a b)) :
    ∃ q, (q ∈ Set.range ac.map ∨ q ∈ Set.range bc.map) ∧ dist (ab.map t) q ≤ 2 * K := by
  have hp : dist a (ab.map t) + dist (ab.map t) b = dist a b := by
    rw [ab.dist_start, ab.dist_finish]
    ring
  by_cases hbranch : 2 * t.val ≤ dist a b + dist a c - dist b c
  · have ht : t.val ≤ dist a c := by linarith [dist_triangle a c b, dist_comm c b]
    let s : Set.Icc (0 : ℝ) (dist a c) := ⟨t.val, t.property.1, ht⟩
    refine ⟨ac.map s, Or.inl (Set.mem_range_self s), ?_⟩
    apply RayBundle.four_point_close_on_side K hK hfour (c := c) hp
    · rwa [ab.dist_start]
    · rw [ac.dist_start, ab.dist_start]
    · rw [ac.dist_finish, ab.dist_start]
  · have hu : dist a b - t.val ≤ dist b c := by
      linarith [dist_triangle a c b, dist_comm c b]
    let s : Set.Icc (0 : ℝ) (dist b c) := ⟨dist a b - t.val,
      sub_nonneg.mpr t.property.2, hu⟩
    refine ⟨bc.map s, Or.inr (Set.mem_range_self s), ?_⟩
    apply RayBundle.four_point_close_on_side K hK hfour (a := b) (b := a) (c := c)
    · simpa only [dist_comm, add_comm] using hp
    · rw [dist_comm b (ab.map t), ab.dist_finish, dist_comm b a]
      linarith
    · rw [bc.dist_start, dist_comm b (ab.map t), ab.dist_finish]
    · rw [bc.dist_finish, dist_comm b (ab.map t), ab.dist_finish]

namespace RayBundle


end RayBundle
