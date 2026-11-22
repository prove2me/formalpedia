-- Prove2me | solution 1 for Paper.Hypergraph.setCoverCost_singleton_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:08:58.741245+00:00
-- url     : https://prove2.me/submissions/045f5f2c-61e0-48b4-9211-d2f11cc672ce

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
theorem _root_.solution (H : Hypergraph) {v : ℕ} (hv : v ∈ H.vertices) :
    H.setCoverCost {v} ≤ 1 := by
  obtain ⟨e, he, hve⟩ := H.no_isolated v hv
  have hh : H.Cover (indicator {v}) (Pi.single e 1) := by
    refine ⟨?_, ?_⟩
    · intro f hf; simp only [Pi.single_apply]; split_ifs <;> norm_num
    · intro u hu
      by_cases huv : u = v
      · subst u; simp [indicator, Pi.single_apply, he, hve]
      · simp only [indicator, mem_singleton, if_neg huv]
        apply sum_nonneg
        intro f hf; simp only [Pi.single_apply]; split_ifs <;> norm_num
  simpa [setCoverCost, Pi.single_apply, he] using H.coverCost_le hh
end Paper.Hypergraph
