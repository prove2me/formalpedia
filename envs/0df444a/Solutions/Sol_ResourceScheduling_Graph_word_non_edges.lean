-- Prove2me | solution 1 for ResourceScheduling.Graph.word_non_edges
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T13:24:53.350165+00:00
-- url     : https://prove2.me/submissions/eac786f5-87f3-4c4b-967e-57745b59d173

import Definitions.Def_ResourceScheduling_Graph_WordProgram

set_option autoImplicit false
open ResourceScheduling.Graph

/-- Natural-index enumeration preserves the original lexicographic resource order. -/
theorem solution (n : ℕ) (bits : List Letter) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj]
    (h : ∀ i j : Fin n, G.Adj i j ↔ bits.getD (i.val * n + j.val) Letter.sep = Letter.one) :
    wordNonEdges n bits = (nonEdgeList G).map (fun p => (p.1.val, p.2.val)) := by
  unfold wordNonEdges nonEdgeList
  rw [← List.map_coe_finRange_eq_range (n := n)]
  simp only [List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def]
  congr 1
  funext i
  rw [List.filter_map]
  simp only [List.map_map, Function.comp_def]
  congr 1
  congr 1
  funext j
  simp only [Fin.lt_def, h]

#print axioms solution
