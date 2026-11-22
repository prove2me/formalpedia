-- Prove2me | solution 1 for Paper.Hypergraph.setCoverCost_biUnion_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:14:18.35567+00:00
-- url     : https://prove2.me/submissions/99285f5d-f413-4fbf-a39f-91d10a119fca

import Definitions.Def_Paper_Formalized
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_Paper_RoundingEstimates
import Theorems.Thm_Paper_Hypergraph_setCoverCost_union_le


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {ι : Type*}
    (I : Finset ι) (S : ι → Finset ℕ) :
    H.setCoverCost (I.biUnion S) ≤ ∑ i ∈ I, H.setCoverCost (S i) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    simp only [biUnion_empty, sum_empty]
    exact (H.coverCost_eq_zero_of_nonpos (x := indicator ∅)
      (fun _ _ => by simp [indicator])).le
  | @insert i I hi ih =>
    rw [biUnion_insert, sum_insert hi]
    exact (H.setCoverCost_union_le _ _).trans (add_le_add_right ih _)
end Paper.Hypergraph
