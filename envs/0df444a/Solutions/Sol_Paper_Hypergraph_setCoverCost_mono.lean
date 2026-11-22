-- Prove2me | solution 1 for Paper.Hypergraph.setCoverCost_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:08:31.324588+00:00
-- url     : https://prove2.me/submissions/120e8bac-13ec-4327-a88b-31267a3cf114

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_coverCost_mono

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {A B : Finset ℕ} (h : A ⊆ B) :
    H.setCoverCost A ≤ H.setCoverCost B := by
  apply H.coverCost_mono
  intro v hv
  by_cases ha : v ∈ A
  · simp [indicator, ha, h ha]
  · simp only [indicator, if_neg ha]; split_ifs <;> norm_num
end Paper.Hypergraph
