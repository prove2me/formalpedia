-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.potts_incident_edge_replacement_chain
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:23:00.017304+00:00
-- url     : https://prove2.me/submissions/74a9af3a-b5c6-4eab-960a-596d13d512f2

import Definitions.Def_ZeroFreeRRG_Hardcore_PottsRowChain
import Mathlib
set_option autoImplicit false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

private theorem row_props {V : Type} [Fintype V] (q : ℕ) (G : SimpleGraph V) (β : ℂ)
    (W : Sym2 V → Fin q → Fin q → ℂ) (hW : ∀ e i j, W e i j = W e j i)
    (hseg : pottsSegmentWeights q G β W) (F : Finset (Sym2 V)) (a b : Fin q) :
    let W' := pottsReplaceRows W F a b
    (∀ e i j, W' e i j = W' e j i) ∧ pottsSegmentWeights q G β W' ∧
      (∀ e ∉ F, ∀ i j, W' e i j = W e i j) ∧
      (∀ e ∈ F, ∀ j, W' e a j = W e b j) := by
  classical
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · intro e i j
    by_cases he : e∈F
    · by_cases hi : i=a <;> by_cases hj : j=a <;> simp [pottsReplaceRows,he,hi,hj,hW]
    · simp [pottsReplaceRows,he,hW]
  · intro e he i j
    by_cases h : e∈F
    · by_cases hi : i=a
      · simpa [pottsReplaceRows,h,hi] using hseg e he b j
      · by_cases hj : j=a
        · simpa [pottsReplaceRows,h,hi,hj] using hseg e he b i
        · simpa [pottsReplaceRows,h,hi,hj] using hseg e he i j
    · simpa [pottsReplaceRows,h] using hseg e he i j
  · intro e he i j
    simp [pottsReplaceRows,he]
  · intro e he j
    simp [pottsReplaceRows,he]


theorem solution {V : Type} [Fintype V] (q : ℕ) (G : SimpleGraph V) (β : ℂ)
    (W : Sym2 V → Fin q → Fin q → ℂ) (hW : ∀ e i j, W e i j = W e j i)
    (hseg : pottsSegmentWeights q G β W) (v : V) (a b : Fin q) :
    ∃ (n : ℕ) (Ws : ℕ → Sym2 V → Fin q → Fin q → ℂ),
      n = G.degree v ∧ Ws 0 = W ∧ Ws n = pottsReplaceRows W (G.incidenceFinset v) a b ∧
      (∀ k, (∀ e i j, Ws k e i j = Ws k e j i) ∧ pottsSegmentWeights q G β (Ws k)) ∧
      (∀ k < n, ∃ e ∈ G.incidenceFinset v,
        (∀ e' ≠ e, ∀ i j, Ws (k+1) e' i j = Ws k e' i j) ∧
        (∀ j, Ws (k+1) e a j = Ws k e b j)) := by
  classical
  let F := G.incidenceFinset v
  let l := F.toList
  let E := fun k : ℕ => (l.take k).toFinset
  let Ws := fun k : ℕ => pottsReplaceRows W (E k) a b
  have hlen : l.length = G.degree v := by dsimp [l,F]; simp [SimpleGraph.card_incidenceFinset_eq_degree]
  have hF0 : E 0 = ∅ := by simp [E]
  have hFn : E (G.degree v) = F := by
    rw [← hlen]
    change (l.take l.length).toFinset = F
    rw [List.take_length]
    simp [l]
  refine ⟨G.degree v, Ws, rfl, ?_, ?_, ?_, ?_⟩
  · funext e i j
    simp [Ws,hF0,pottsReplaceRows]
  · simp only [Ws,hFn,F]
  · intro k
    have hh := row_props q G β W hW hseg (E k) a b
    exact ⟨hh.1,hh.2.1⟩
  · intro k hk
    have hkl : k < l.length := by rw [hlen]; exact hk
    let e := l[k]
    have hein : e ∈ F := by
      change l[k] ∈ F
      exact Finset.mem_toList.mp (List.getElem_mem hkl)
    have hn : e ∉ E k := by
      intro he
      have hm : e ∈ l.take k := List.mem_toFinset.mp he
      have hn' : (l.take (k+1)).Nodup := (List.take_sublist (k+1) l).nodup F.nodup_toList
      rw [List.take_succ_eq_append_getElem hkl] at hn'
      have hdis := (List.nodup_append.mp hn').2.2 e hm e (by simp [e])
      exact hdis rfl
    have hE : E (k+1) = insert e (E k) := by
      dsimp [E,e]
      rw [List.take_succ_eq_append_getElem hkl,List.toFinset_append]
      simp
    refine ⟨e,hein,?_,?_⟩
    · intro e' he' i j
      dsimp [Ws]
      rw [hE]
      simp [pottsReplaceRows,Finset.mem_insert,he']
    · intro j
      dsimp [Ws]
      rw [hE]
      simp [pottsReplaceRows,hn]
