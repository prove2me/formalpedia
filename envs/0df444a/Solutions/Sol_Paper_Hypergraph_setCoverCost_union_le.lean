-- Prove2me | solution 1 for Paper.Hypergraph.setCoverCost_union_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:08:09.399515+00:00
-- url     : https://prove2.me/submissions/32091756-b77f-4f13-8970-454de72d67b0

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_coverCost_mono
import Theorems.Thm_Paper_Hypergraph_coverCost_add_le

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) (A B : Finset ℕ) :
    H.setCoverCost (A ∪ B) ≤ H.setCoverCost A + H.setCoverCost B := by
  apply le_trans _ (H.coverCost_add_le (indicator A) (indicator B))
  apply H.coverCost_mono
  intro v hv
  simp only [indicator, mem_union, Pi.add_apply]
  split_ifs <;> simp_all
end Paper.Hypergraph
