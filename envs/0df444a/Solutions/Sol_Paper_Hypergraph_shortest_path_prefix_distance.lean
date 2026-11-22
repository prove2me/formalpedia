-- Prove2me | solution 1 for Paper.Hypergraph.shortest_path_prefix_distance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:01:50.65285+00:00
-- url     : https://prove2.me/submissions/b1039c7b-18e4-430c-81c4-445ef0e19779

import Definitions.Def_Paper_RoundingGeometry
import Mathlib.Combinatorics.SimpleGraph.Metric
import Definitions.Def_Paper_RoundingPaths

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution {G : SimpleGraph ℕ} {u v : ℕ}
    (p : G.Walk u v) (hp : p.length = G.dist u v) {i : ℕ} (hi : i ≤ p.length) :
    G.dist u (p.getVert i) = i := by
  have ht := G.dist_le (p.take i)
  have hd := G.dist_le (p.drop i)
  have htri := (p.take i).reachable.dist_triangle_left v
  rw [SimpleGraph.Walk.take_length, min_eq_left hi] at ht
  rw [SimpleGraph.Walk.drop_length] at hd
  omega
end Paper.Hypergraph
