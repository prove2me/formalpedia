-- Prove2me | solution 1 for Paper.Hypergraph.finiteEdgeDistance_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:11:17.916966+00:00
-- url     : https://prove2.me/submissions/c7d24b04-4f8d-4337-b931-e639847ee508

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
theorem _root_.solution (H : Hypergraph) (e f : ℕ) {x y : ℕ → ℝ}
    (hxy : ∀ v ∈ H.vertices, x v = y v) : H.finiteEdgeDistance e f x = H.finiteEdgeDistance e f y := by
  apply Finset.inf'_congr _ rfl
  intro o ho
  cases o with
  | none => rfl
  | some S =>
    have hS : S ⊆ H.vertices := by
      simp only [separatorPathOptions, mem_insert, Option.some_ne_none, false_or,
        mem_image, Option.some.injEq, exists_eq_right, mem_filter, mem_powerset] at ho
      exact ho.1
    exact sum_congr rfl (fun v hv => hxy v (hS hv))
end Paper.Hypergraph
