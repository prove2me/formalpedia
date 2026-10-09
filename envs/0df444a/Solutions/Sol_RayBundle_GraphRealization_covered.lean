-- Prove2me | solution 1 for RayBundle.GraphRealization.covered
-- status  : ACCEPTED   (prove)
-- author  : @jawneeboy
-- created : 2026-10-08T18:57:03.189164+00:00
-- url     : https://prove2.me/submissions/caa5d449-2a5b-4e15-bba2-b486ac044d56

import Definitions.Def_RayBundle_UnitEdgeGraphGeometry
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Gluing
import Mathlib.Topology.MetricSpace.Isometry

-- Source: RayBundle.Thm_Cayley_UnitEdgeRealization_stage_covered
namespace RayBundle

universe u

theorem UnitEdgeRealization.stage_covered {V : Type u} [MetricSpace V]
    (a b : ℕ → V) (hab : ∀ n, dist (a n) (b n) = 1) (n : ℕ) :
    ∀ x : (UnitEdgeStage.sequence a b hab n).carrier,
      (∃ v, Metric.toInductiveLimit (UnitEdgeStage.sequenceStep_isometry a b hab) n x =
        vertex a b hab v) ∨
      ∃ k t, Metric.toInductiveLimit (UnitEdgeStage.sequenceStep_isometry a b hab) n x =
        edge a b hab k t := by
  induction n with
  | zero => exact fun x => Or.inl ⟨x, rfl⟩
  | succ n ih =>
    intro x
    refine Quotient.inductionOn x ?_
    intro y
    rcases y with y | t
    · have he := congrFun (Metric.toInductiveLimit_commute
        (UnitEdgeStage.sequenceStep_isometry a b hab) n) y
      change Metric.toInductiveLimit (UnitEdgeStage.sequenceStep_isometry a b hab) (n + 1)
        (UnitEdgeStage.sequenceStep a b hab n y) =
        Metric.toInductiveLimit (UnitEdgeStage.sequenceStep_isometry a b hab) n y at he
      rcases ih y with ⟨v, hv⟩ | ⟨k, t, ht⟩
      · exact Or.inl ⟨v, he.trans hv⟩
      · exact Or.inr ⟨k, t, he.trans ht⟩
    · exact Or.inr ⟨n, t, rfl⟩

end RayBundle

-- Source: RayBundle.Thm_Cayley_UnitEdgeRealization_covered
namespace RayBundle

universe u

theorem UnitEdgeRealization.covered {V : Type u} [MetricSpace V]
    (a b : ℕ → V) (hab : ∀ n, dist (a n) (b n) = 1) (p : UnitEdgeRealization a b hab) :
    (∃ v, p = vertex a b hab v) ∨ ∃ n t, p = edge a b hab n t := by
  refine Quotient.inductionOn p ?_
  rintro ⟨n, x⟩
  exact stage_covered a b hab n x

end RayBundle

-- Source: RayBundle.Thm_Cayley_GraphRealization_covered
namespace RayBundle

universe u

end RayBundle

open RayBundle
universe u
theorem solution {V : Type u} (T : SimpleGraph V)
    (hT : T.Connected) (e : ℕ ≃ T.edgeSet) (p : RayBundle.GraphRealization T hT e) :
    (∃ v, p = RayBundle.GraphRealization.vertex T hT e v) ∨ ∃ n t, p = RayBundle.GraphRealization.edge T hT e n t := by
  let := RayBundle.connectedGraphMetric T hT
  exact RayBundle.UnitEdgeRealization.covered _ _ _ p

namespace RayBundle


end RayBundle
