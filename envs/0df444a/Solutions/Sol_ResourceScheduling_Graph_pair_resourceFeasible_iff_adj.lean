-- Prove2me | solution 1 for ResourceScheduling.Graph.pair_resourceFeasible_iff_adj
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:19:56.806693+00:00
-- url     : https://prove2.me/submissions/959423f3-afca-470b-ab54-21515a836077

import Mathlib
import Definitions.Def_ResourceScheduling_Graph_Construction

namespace ResourceScheduling.Graph

theorem aux_prf_mem {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (p : Fin N × Fin N) :
    p ∈ nonEdgeList G ↔ p.1 < p.2 ∧ ¬ G.Adj p.1 p.2 := by
  obtain ⟨a, b⟩ := p
  simp [nonEdgeList]

end ResourceScheduling.Graph

open ResourceScheduling.Graph

theorem solution {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (y m : ℕ) (q : Fin m → ℝ) (hq : ∀ i, 0 < q i) (j k : Fin N) (hjk : j ≠ k) :
    ((construct G y).toInstance m q hq).ResourceFeasibleSet {j, k} ↔ G.Adj j k := by
  show (∀ h : Fin (nonEdgeList G).length, ∑ i ∈ ({j, k} : Finset (Fin N)),
      (if i = ((nonEdgeList G).get h).1 ∨ i = ((nonEdgeList G).get h).2 then 1 else 0) ≤ 1) ↔ _
  simp only [Finset.sum_pair hjk]
  constructor
  · intro h
    by_contra hadj
    have key : ∀ a b : Fin N, a < b → ¬ G.Adj a b → ({a, b} : Set (Fin N)) = {j, k} → False := by
      intro a b hab hn hs
      have hm : (a, b) ∈ nonEdgeList G := (aux_prf_mem G _).2 ⟨hab, hn⟩
      obtain ⟨i, hi⟩ := List.get_of_mem hm
      have := h i
      rw [hi] at this
      have hj : j = a ∨ j = b := by
        have : j ∈ ({a, b} : Set (Fin N)) := by rw [hs]; simp
        simpa using this
      have hk : k = a ∨ k = b := by
        have : k ∈ ({a, b} : Set (Fin N)) := by rw [hs]; simp
        simpa using this
      simp only [hj, hk, if_true] at this
      omega
    rcases lt_or_gt_of_ne hjk with hlt | hlt
    · exact key j k hlt hadj rfl
    · exact key k j hlt (fun h' => hadj h'.symm) (Set.pair_comm _ _)
  · intro hadj h
    have hm := (aux_prf_mem G _).1 (List.get_mem (nonEdgeList G) h)
    obtain ⟨hlt, hn⟩ := hm
    set a := ((nonEdgeList G).get h).1
    set b := ((nonEdgeList G).get h).2
    by_cases hj : j = a ∨ j = b
    · by_cases hk : k = a ∨ k = b
      · exfalso
        rcases hj with hj | hj <;> rcases hk with hk | hk
        · exact hjk (hj.trans hk.symm)
        · subst hj hk; exact hn hadj
        · subst hj hk; exact hn hadj.symm
        · exact hjk (hj.trans hk.symm)
      · simp only [hj, hk, if_true, if_false]; omega
    · simp only [hj, if_false]; split <;> omega
