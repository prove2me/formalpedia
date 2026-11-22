-- Prove2me | solution 1 for Paper.Hypergraph.cover_cap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:56:08.85758+00:00
-- url     : https://prove2.me/submissions/580c86a9-a439-48f5-a52c-ec0ad74d95af

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {x y : ℕ → ℝ} (hx : H.UnitDemand x)
    (hy : H.Cover x y) : H.Cover x (fun e => min (y e) 1) := by
  refine ⟨fun e he => le_min (hy.1 e he) (by norm_num), ?_⟩
  intro v hv
  by_cases h : ∃ e ∈ H.edges.filter (fun e => v ∈ H.edge e), 1 ≤ y e
  · obtain ⟨e, he, he1⟩ := h
    calc
      x v ≤ 1 := (hx v hv).2
      _ = min (y e) 1 := (min_eq_right he1).symm
      _ ≤ ∑ f ∈ H.edges.filter (fun f => v ∈ H.edge f), min (y f) 1 :=
        single_le_sum (fun f hf => le_min (hy.1 f (mem_filter.mp hf).1)
          (by norm_num)) he
  · convert hy.2 v hv using 1
    apply sum_congr rfl
    intro e he
    exact min_eq_left (le_of_not_ge (fun h1 => h ⟨e, he, h1⟩))
end Paper.Hypergraph
