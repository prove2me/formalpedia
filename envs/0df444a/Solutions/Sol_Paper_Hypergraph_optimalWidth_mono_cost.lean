-- Prove2me | solution 1 for Paper.Hypergraph.optimalWidth_mono_cost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:07:45.010612+00:00
-- url     : https://prove2.me/submissions/1b636ef6-6647-4ad3-8533-9b961a6623d1

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_optimalWidth_le_bagWidth

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) (b c : Finset ℕ → ℝ)
    (hb : ∀ S ⊆ H.vertices, 0 ≤ b S)
    (hbc : ∀ S ⊆ H.vertices, b S ≤ c S) : H.optimalWidth b ≤ H.optimalWidth c := by
  refine le_csInf ⟨_, 0, H.oneBag, rfl⟩ ?_
  rintro r ⟨n, D, rfl⟩
  apply (H.optimalWidth_le_bagWidth b hb D).trans
  refine csSup_le ⟨_, 0, rfl⟩ ?_
  rintro r ⟨t, rfl⟩
  exact (hbc _ (D.bag_subset t)).trans (le_csSup (Set.finite_range _).bddAbove ⟨t, rfl⟩)
end Paper.Hypergraph
