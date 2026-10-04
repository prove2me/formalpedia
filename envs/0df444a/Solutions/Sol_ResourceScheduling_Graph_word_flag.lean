-- Prove2me | solution 1 for ResourceScheduling.Graph.word_flag
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T14:51:13.273547+00:00
-- url     : https://prove2.me/submissions/870bad71-8723-4d49-9a0e-653c08f8d9bb

import Definitions.Def_ResourceScheduling_Graph_WordProgram
import Definitions.Def_ResourceScheduling_Graph_RAMParse
import Theorems.Thm_ResourceScheduling_Graph_split_ones

set_option autoImplicit false
open ResourceScheduling.Graph

theorem solution (w bits : List Letter) (N a g : ℕ)
    (hn : N = 3 * (splitOnes w).1) (hw : bits = (splitOnes w).2.tail)
    (ha : a = if (splitOnes w).2 ≠ [] ∧ bits.length = N * N then 1 else 0)
    (hg : g = if ∀ i < N, bits.getD (i * N + i) Letter.sep ≠ Letter.one ∧
      ∀ j < N, bits.getD (i * N + j) Letter.sep = Letter.one →
        bits.getD (j * N + i) Letter.sep = Letter.one then a else 0) :
    wordProgram w = if 0 < g then emitQ2Word (splitOnes w).1 (splitOnes w).2.tail else [] := by
  let C := ∀ i < N, bits.getD (i * N + i) Letter.sep ≠ Letter.one ∧
    ∀ j < N, bits.getD (i * N + j) Letter.sep = Letter.one →
      bits.getD (j * N + i) Letter.sep = Letter.one
  have hcheck : checkGraphBody N bits = true ↔ bits.length = N * N ∧ C := by
    simp [checkGraphBody, C, List.all_eq_true, imp_iff_not_or]
  have hflag : 0 < g ↔ (splitOnes w).2 ≠ [] ∧ checkGraphBody N bits = true := by
    rw [hg, ha, hcheck]
    change (0 < if C then (if (splitOnes w).2 ≠ [] ∧ bits.length = N * N then 1 else 0) else 0) ↔ _
    by_cases hc : C <;> by_cases hr : (splitOnes w).2 = [] <;>
      by_cases hl : bits.length = N * N <;> simp [hc, hr, hl]
  rw [wordProgram, (split_ones w).2.2.2]
  by_cases hr : (splitOnes w).2 = []
  · have hbad : ¬0 < g := by rw [hflag]; simp [hr]
    simp [hr,hbad]
  · have hgood : (0 < g) ↔ checkGraphBody N bits = true := by simpa [hr] using hflag
    simp only [hr, if_false]
    simp only [hgood, hn, hw]

#print axioms solution
