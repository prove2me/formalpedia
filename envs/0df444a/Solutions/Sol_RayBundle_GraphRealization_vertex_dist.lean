-- Prove2me | solution 1 for RayBundle.GraphRealization.vertex_dist
-- status  : ACCEPTED   (prove)
-- author  : @jawneeboy
-- created : 2026-10-08T18:57:02.134725+00:00
-- url     : https://prove2.me/submissions/63cdaf36-d5a8-4530-980d-ca5199d1ab93

import Definitions.Def_RayBundle_UnitEdgeGraphGeometry
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Gluing
import Mathlib.Topology.MetricSpace.Isometry

-- Source: RayBundle.Thm_Cayley_UnitEdgeRealization_vertex_isometry
namespace RayBundle

universe u

theorem UnitEdgeRealization.vertex_isometry {V : Type u} [MetricSpace V]
    (a b : ℕ → V) (hab : ∀ n, dist (a n) (b n) = 1) : Isometry (vertex a b hab) :=
  Metric.toInductiveLimit_isometry (UnitEdgeStage.sequenceStep_isometry a b hab) 0

end RayBundle

-- Source: RayBundle.Thm_Cayley_GraphRealization_vertex_dist
namespace RayBundle

universe u

end RayBundle

open RayBundle
universe u
theorem solution {V : Type u} (T : SimpleGraph V)
    (hT : T.Connected) (e : ℕ ≃ T.edgeSet) (v w : V) :
    dist (RayBundle.GraphRealization.vertex T hT e v) (RayBundle.GraphRealization.vertex T hT e w) = (T.dist v w : ℝ) := by
  let := RayBundle.connectedGraphMetric T hT
  exact (RayBundle.UnitEdgeRealization.vertex_isometry _ _ _).dist_eq v w

namespace RayBundle


end RayBundle
