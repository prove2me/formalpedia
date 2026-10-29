-- Prove2me | solution 1 for SensitivityGraphCheck.search_iff_word
-- status  : ACCEPTED   (prove)
-- author  : @dmilosch
-- created : 2026-10-29T00:24:08.029564+00:00
-- url     : https://prove2.me/submissions/03325647-78cf-41b7-96cd-b56d918dacca

import Definitions.Def_SensitivityGraphCheck
import Theorems.Thm_SensitivityVariableFrontier_search_correct

set_option autoImplicit false

namespace SensitivityGraphCheck
open SensitivityProfileCycle SensitivityProfileSearch SensitivityVariableWord

theorem valid_iff (D : RawData) : valid D = true ↔ D.Valid := by
  simp [valid]

theorem filter_eq_of_iff {α : Type} (s : Finset α) (p q : α → Prop)
    (dp : DecidablePred p) (dq : DecidablePred q)
    (h : ∀ x ∈ s, p x ↔ q x) :
    @Finset.filter α p dp s = @Finset.filter α q dq s :=
  @Finset.filter_congr α p q dp dq s h

theorem ofGraph_valid (G : GraphData) : (ofGraph G).Valid := by
  classical
  refine ⟨G.vertices_gt_one, G.ordinary_ge_four, G.source_ge_four, G.cutoff_zero,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [ofGraph] using G.loopless
  · intro i j hij
    simpa [ofGraph] using G.complement hij
  · intro i
    convert G.outdegree i using 1
    · congr 1
      apply filter_eq_of_iff
      intro j hj
      simp only [ofGraph, decide_eq_true_eq]
    · rfl
  · intro I colors hh
    apply G.coherent I colors
    intro i hi j hj hadj
    apply hh i hi j hj
    simpa [ofGraph] using hadj
  · intro q I colors hh
    apply G.defect q I colors
    intro i hi
    convert hh i hi using 1
    congr 1
    apply filter_eq_of_iff
    intro j hj
    simp only [ofGraph, decide_eq_true_eq]
  · intro I colors hs hh
    apply G.source I colors
    · obtain ⟨s, hsI, hs⟩ := hs
      refine ⟨s, hsI, ?_⟩
      intro j hj hjs
      simpa [ofGraph] using hs j hj hjs
    · intro i hi
      convert hh i hi using 1
      congr 1
      apply filter_eq_of_iff
      intro j hj
      simp only [ofGraph, decide_eq_true_eq]

theorem ofGraph_step (G : GraphData) (h : (ofGraph G).Valid)
    {n : ℕ} (C : Recipe n) (P : Profile n) :
    SensitivityVariableWord.step ((ofGraph G).toGraph h) C P =
      SensitivityVariableWord.step G C P := rfl

theorem ofGraph_run (G : GraphData) (h : (ofGraph G).Valid)
    {n : ℕ} (word : List (Recipe n)) (P : Profile n) :
    SensitivityVariableWord.run ((ofGraph G).toGraph h) word P =
      SensitivityVariableWord.run G word P := rfl

theorem ofGraph_crosses (G : GraphData) (h : (ofGraph G).Valid)
    {n : ℕ} (word : List (Recipe n)) :
    SensitivityVariableWord.Crosses215 ((ofGraph G).toGraph h) word ↔
      SensitivityVariableWord.Crosses215 G word := Iff.rfl

theorem raw_iff_graph :
    (∃ (D : RawData) (h : D.Valid) (n : ℕ)
      (word : List (Recipe (n+1))), Crosses215 (D.toGraph h) word) ↔
    ∃ (G : GraphData) (n : ℕ) (word : List (Recipe (n+1))),
      Crosses215 G word := by
  constructor
  · rintro ⟨D,h,n,word,hw⟩
    exact ⟨D.toGraph h,n,word,hw⟩
  · rintro ⟨G,n,word,hw⟩
    exact ⟨ofGraph G,ofGraph_valid G,n,word,hw⟩

end SensitivityGraphCheck


namespace SensitivityGraphCheck
open SensitivityProfileCycle SensitivityVariableWord

theorem checked_search_iff_word :
    (∃ (D : RawData) (n k : ℕ), succeeds D (n + 1) k = true) ↔
    ∃ (G : GraphData) (n : ℕ) (word : List (Recipe (n + 1))),
      Crosses215 G word := by
  constructor
  · rintro ⟨D, n, k, hs⟩
    unfold succeeds at hs
    split at hs
    next h =>
      obtain ⟨word, _, hw⟩ :=
        (SensitivityVariableFrontier.search_correct (D.toGraph h) (n + 1) k).mp hs
      exact ⟨D.toGraph h, n, word, hw⟩
    next h => simp at hs
  · rintro ⟨G, n, word, hw⟩
    let D := ofGraph G
    have hD : D.Valid := ofGraph_valid G
    refine ⟨D, n, word.length, ?_⟩
    simp only [succeeds, dif_pos hD]
    apply (SensitivityVariableFrontier.search_correct (D.toGraph hD) (n + 1) word.length).mpr
    exact ⟨word, rfl, (ofGraph_crosses G hD word).mpr hw⟩

end SensitivityGraphCheck

theorem solution :
    (∃ (D : SensitivityGraphCheck.RawData) (n k : ℕ),
      SensitivityGraphCheck.succeeds D (n + 1) k = true) ↔
    ∃ (G : SensitivityVariableWord.GraphData) (n : ℕ)
      (word : List (SensitivityProfileCycle.Recipe (n + 1))),
      SensitivityVariableWord.Crosses215 G word :=
  SensitivityGraphCheck.checked_search_iff_word

#print axioms solution
