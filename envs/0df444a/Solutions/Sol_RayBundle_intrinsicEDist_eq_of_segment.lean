-- Prove2me | solution 1 for RayBundle.intrinsicEDist_eq_of_segment
-- status  : ACCEPTED   (prove)
-- author  : @jawneeboy
-- created : 2026-10-08T19:38:27.915886+00:00
-- url     : https://prove2.me/submissions/2037db93-6224-4b6d-8a3e-729f7e211002

import Definitions.Def_RayBundle_MetricPathGeometry
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.Path

-- Source: RayBundle.Def_Cayley_MetricSegment_toPath
namespace RayBundle

/-- Normalize an arc-length segment to a continuous path on the unit interval. -/
noncomputable def MetricSegment.toPath {X : Type*} [MetricSpace X] {a b : X}
    (c : MetricSegment a b) : _root_.Path a b := by
  let f : unitInterval → Set.Icc (0 : ℝ) (dist a b) := fun u =>
    ⟨dist a b * u.val, by
      constructor
      · exact mul_nonneg dist_nonneg u.property.1
      · nlinarith [u.property.2, dist_nonneg (x := a) (y := b)]⟩
  have hf : Continuous f := by dsimp [f]; fun_prop
  refine
    { toFun := c.map ∘ f
      continuous_toFun := c.isometry.continuous.comp hf
      source' := ?_
      target' := ?_ }
  · have h : f 0 = ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ := Subtype.ext (by simp [f])
    exact (congrArg c.map h).trans c.start
  · have h : f 1 = ⟨dist a b, ⟨dist_nonneg, le_rfl⟩⟩ := Subtype.ext (by simp [f])
    exact (congrArg c.map h).trans c.finish

end RayBundle

-- Source: RayBundle.Thm_Cayley_MetricSegment_toPath_dist
namespace RayBundle

theorem MetricSegment.toPath_dist {X : Type*} [MetricSpace X] {a b : X}
    (c : MetricSegment a b) (s t : unitInterval) :
    dist (c.toPath s) (c.toPath t) = dist a b * dist s t := by
  change dist (c.map _) (c.map _) = _
  rw [c.isometry.dist_eq]
  change |dist a b * s.val - dist a b * t.val| = dist a b * |s.val - t.val|
  rw [← mul_sub, abs_mul, abs_of_nonneg dist_nonneg]

end RayBundle

-- Source: RayBundle.Thm_Cayley_eVariationOn_eq_of_edist_eq
namespace RayBundle

/-- Variation depends only on pairwise distances on the parameter set. -/
theorem eVariationOn_eq_of_edist_eq {α E F : Type*} [LinearOrder α]
    [PseudoEMetricSpace E] [PseudoEMetricSpace F] (f : α → E) (g : α → F) (s : Set α)
    (h : ∀ x ∈ s, ∀ y ∈ s, edist (f x) (f y) = edist (g x) (g y)) :
    eVariationOn f s = eVariationOn g s := by
  unfold eVariationOn
  apply iSup_congr
  intro p
  apply Finset.sum_congr rfl
  intro i _
  exact h _ (p.2.property.2 _) _ (p.2.property.2 _)

end RayBundle

-- Source: RayBundle.Thm_Cayley_MetricSegment_toPath_length
namespace RayBundle

/-- The normalized path attains the endpoint distance, also for a zero-length segment. -/
theorem MetricSegment.toPath_length {X : Type*} [MetricSpace X] {a b : X}
    (c : MetricSegment a b) : metricPathLength c.toPath = edist a b := by
  let f : unitInterval → ℝ := fun u => dist a b * u.val
  have hp (s t : unitInterval) : edist (c.toPath s) (c.toPath t) = edist (f s) (f t) := by
    rw [edist_dist, edist_dist, c.toPath_dist]
    congr 1
    change dist a b * |s.val - t.val| = |dist a b * s.val - dist a b * t.val|
    rw [← mul_sub, abs_mul, abs_of_nonneg dist_nonneg]
  change eVariationOn c.toPath Set.univ = _
  rw [eVariationOn_eq_of_edist_eq c.toPath f Set.univ (fun s _ t _ => hp s t)]
  have hm : MonotoneOn f Set.univ := fun s _ t _ h =>
    mul_le_mul_of_nonneg_left h dist_nonneg
  have hv := hm.eVariationOn_eq (a := (0 : unitInterval)) (b := (1 : unitInterval))
    (Set.mem_univ _) (Set.mem_univ _)
  simpa [f, ← unitInterval.univ_eq_Icc, edist_dist] using hv

end RayBundle

-- Source: RayBundle.Thm_Cayley_edist_le_metricPathLength
namespace RayBundle

/-- Every continuous path has length at least the distance between its endpoints. -/
theorem edist_le_metricPathLength {X : Type*} [PseudoEMetricSpace X] {a b : X}
    (γ : _root_.Path a b) : edist a b ≤ metricPathLength γ := by
  simpa only [metricPathLength, γ.source, γ.target] using
    eVariationOn.edist_le γ (Set.mem_univ (0 : unitInterval))
      (Set.mem_univ (1 : unitInterval))

end RayBundle

-- Source: RayBundle.Thm_Cayley_edist_le_intrinsicEDist
namespace RayBundle

theorem edist_le_intrinsicEDist {X : Type*} [PseudoEMetricSpace X] (a b : X) :
    edist a b ≤ intrinsicEDist a b :=
  le_iInf fun γ => edist_le_metricPathLength γ

end RayBundle

-- Source: RayBundle.Thm_Cayley_intrinsicEDist_eq_of_segment
namespace RayBundle

end RayBundle

open RayBundle
universe u
/-- A geodesic makes the metric distance equal to the intrinsic path distance. -/
theorem solution {X : Type*} [MetricSpace X] {a b : X}
    (c : RayBundle.MetricSegment a b) : RayBundle.intrinsicEDist a b = edist a b := by
  apply le_antisymm _ (RayBundle.edist_le_intrinsicEDist a b)
  exact (iInf_le (fun γ : _root_.Path a b => RayBundle.metricPathLength γ) c.toPath).trans_eq
    c.toPath_length

namespace RayBundle


end RayBundle
