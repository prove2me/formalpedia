-- Prove2me | solution 1 for RayBundle.GraphRealization.edge_isometry
-- status  : ACCEPTED   (prove)
-- author  : @jawneeboy
-- created : 2026-10-08T18:57:16.305779+00:00
-- url     : https://prove2.me/submissions/a9d74f3b-525c-4921-a972-f3f8204b5729

import Definitions.Def_RayBundle_UnitEdgeGraphGeometry
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Gluing
import Mathlib.Topology.MetricSpace.Isometry

-- Source: RayBundle.Thm_Cayley_UnitEdgeRealization_edge_isometry
namespace RayBundle

universe u

theorem UnitEdgeRealization.edge_isometry {V : Type u} [MetricSpace V]
    (a b : ℕ → V) (hab : ∀ n, dist (a n) (b n) = 1) (n : ℕ) :
    Isometry (edge a b hab n) :=
  (Metric.toInductiveLimit_isometry (UnitEdgeStage.sequenceStep_isometry a b hab) (n + 1)).comp
    ((UnitEdgeStage.sequence a b hab n).attach (a n) (b n) (hab n)).edgeIsometry

end RayBundle

-- Source: RayBundle.Thm_Cayley_GraphRealization_edge_isometry
namespace RayBundle

universe u

end RayBundle

open RayBundle
universe u
theorem solution {V : Type u} (T : SimpleGraph V)
    (hT : T.Connected) (e : ℕ ≃ T.edgeSet) (n : ℕ) : Isometry (RayBundle.GraphRealization.edge T hT e n) := by
  let := RayBundle.connectedGraphMetric T hT
  exact RayBundle.UnitEdgeRealization.edge_isometry _ _ _ n

namespace RayBundle


end RayBundle
