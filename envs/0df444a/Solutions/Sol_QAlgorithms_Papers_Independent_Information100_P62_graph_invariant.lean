-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P62.graph_invariant
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T08:32:20.305977+00:00
-- url     : https://prove2.me/submissions/3f16c533-1923-4af2-8caf-1dfee12442b3

import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_graph_transmission

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.24, Corollary 3.7: transmission is a graph invariant. -/
theorem solution [Nonempty I] [Nonempty O] [Nonempty J] [Nonempty K]
    (F : Superop I O) (G : Superop J K) (hF : IsChannel F) (hG : IsChannel G)
    (h : GraphIso (graph F) (graph G)) : transmission F = transmission G  := by
  ext A
  change Transmits F A ↔ Transmits G A
  exact ⟨graph_transmission F G hF hG h.1 A,
    graph_transmission G F hG hF h.2 A⟩

