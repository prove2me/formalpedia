-- Prove2me | solution 1 for Paper.Hypergraph.concave_finiteEdgeDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:10:52.007077+00:00
-- url     : https://prove2.me/submissions/b522bf2a-4cb5-460d-8ca7-30dbdf547e39

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
theorem _root_.solution (H : Hypergraph) (e f : ℕ) :
    ConcaveOn ℝ Set.univ (H.finiteEdgeDistance e f) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  apply Finset.le_inf'
  intro o ho
  have hxle := Finset.inf'_le (fun o => pathOptionCost o x) ho
  have hyle := Finset.inf'_le (fun o => pathOptionCost o y) ho
  have hc : pathOptionCost o (a • x + b • y) =
      a * pathOptionCost o x + b * pathOptionCost o y := by
    cases o with
    | none => simpa [pathOptionCost] using hab.symm
    | some S => simp [pathOptionCost, Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, mul_sum]
  change a * H.finiteEdgeDistance e f x + b * H.finiteEdgeDistance e f y ≤ _
  rw [hc]
  exact add_le_add (mul_le_mul_of_nonneg_left hxle ha) (mul_le_mul_of_nonneg_left hyle hb)
end Paper.Hypergraph
