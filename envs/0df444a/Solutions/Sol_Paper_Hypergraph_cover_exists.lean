-- Prove2me | solution 1 for Paper.Hypergraph.cover_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:52:13.691545+00:00
-- url     : https://prove2.me/submissions/8037ef44-e046-47ef-beae-13baa036c97b

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
theorem _root_.solution (H : Hypergraph) (x : ℕ → ℝ) : ∃ y, H.Cover x y := by
  let M : ℝ := ∑ v ∈ H.vertices, max 0 (x v)
  have hM : 0 ≤ M := sum_nonneg (fun _ _ => le_max_left _ _)
  refine ⟨fun _ => M, (fun _ _ => hM), ?_⟩
  intro v hv
  obtain ⟨e, he, hve⟩ := H.no_isolated v hv
  calc
    x v ≤ max 0 (x v) := le_max_right _ _
    _ ≤ M := single_le_sum (fun _ _ => le_max_left _ _) hv
    _ ≤ ∑ f ∈ H.edges.filter (fun f => v ∈ H.edge f), M :=
      single_le_sum (fun _ _ => hM) (mem_filter.mpr ⟨he, hve⟩)
end Paper.Hypergraph
