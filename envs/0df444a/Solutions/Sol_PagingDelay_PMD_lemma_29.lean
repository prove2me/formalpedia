-- Prove2me | solution 1 for PagingDelay.PMD.lemma_29
-- status  : ACCEPTED   (prove)
-- author  : @licsth
-- created : 2026-11-14T08:45:44.096203+00:00
-- url     : https://prove2.me/submissions/2e4e7b67-1d1b-43c8-bbae-cfe775417cad

import Definitions.Def_PagingDelay_PMD_Path

/-!
Lemma 29 (lightest weights of offline period caches). For every distinct event time `t` of a
lazy schedule, the last event at time `t` fetches a page `q` of the cache after `t`, so its fetch
cost is at least `w_q ≥ w_min(cache after t)`. Distinct times have distinct last events.
-/

set_option linter.unusedVariables false

namespace PagingDelay.PMD.Lemma29

open PagingDelay.PMD

variable {n : ℕ}

/-- `minWeight` is at most the weight of any page of the set. -/
lemma minWeight_le (w : Fin n → ℝ) (C : Finset (Fin n)) {q : Fin n} (hq : q ∈ C) :
    minWeight w C ≤ w q := by
  unfold minWeight
  have hmem : w q ∈ C.toList.map w := List.mem_map.2 ⟨q, Finset.mem_toList.2 hq, rfl⟩
  generalize C.toList.map w = l at hmem ⊢
  generalize w q = a at hmem ⊢
  induction l with
  | nil => simp at hmem
  | cons x l ih =>
    simp only [List.foldr_cons, Option.getD_some]
    split
    · next heq =>
      rcases List.mem_cons.mp hmem with rfl | h
      · exact le_rfl
      · cases l with
        | nil => simp at h
        | cons y l' => simp at heq
    · next b heq =>
      rcases List.mem_cons.mp hmem with rfl | h
      · exact min_le_left _ _
      · have := ih h
        rw [heq, Option.getD_some] at this
        exact (min_le_right _ _).trans this

lemma ofReal_list_sum_le (l : List ℝ) :
    ENNReal.ofReal l.sum ≤ (l.map ENNReal.ofReal).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.sum_cons, List.map_cons]
    exact ENNReal.ofReal_add_le.trans (add_le_add le_rfl ih)

lemma cacheAfter_cons (c : Finset (Fin n)) (e : CacheEvent n) (es : Schedule n) {t : ℝ}
    (ht : e.time ≤ t) : cacheAfter c (e :: es) t = cacheAfter e.cache es t := by
  unfold cacheAfter
  rw [List.filter_cons_of_pos (by simpa using ht), List.map_cons, List.getLastD_cons]

/-- The key estimate, by induction along the schedule. -/
lemma key (w : Fin n → ℝ) :
    ∀ (c : Finset (Fin n)) (s : Schedule n), s.Pairwise (fun e f => e.time ≤ f.time) →
      LazyFrom c s →
      ((s.map CacheEvent.time).dedup.map
          (fun t => ENNReal.ofReal (minWeight w (cacheAfter c s t)))).sum ≤
        fetchCostFrom w c s
  | c, [], _, _ => by simp
  | c, e :: es, hs, hl => by
    rw [List.pairwise_cons] at hs
    simp only [LazyFrom] at hl
    obtain ⟨⟨p, hp, q, hq, he⟩, hl'⟩ := hl
    have ih := key w e.cache es hs.2 hl'
    have hge : ∀ t ∈ es.map CacheEvent.time, e.time ≤ t := by
      intro t ht
      obtain ⟨f, hf, rfl⟩ := List.mem_map.1 ht
      exact hs.1 f hf
    have hcongr : ∀ t ∈ (es.map CacheEvent.time).dedup,
        ENNReal.ofReal (minWeight w (cacheAfter c (e :: es) t)) =
          ENNReal.ofReal (minWeight w (cacheAfter e.cache es t)) := fun t ht => by
      rw [cacheAfter_cons c e es (hge t (List.mem_dedup.1 ht))]
    simp only [List.map_cons, fetchCostFrom]
    by_cases hmem : e.time ∈ es.map CacheEvent.time
    · rw [List.dedup_cons_of_mem hmem, List.map_congr_left hcongr]
      exact ih.trans le_add_self
    · rw [List.dedup_cons_of_notMem hmem, List.map_cons, List.sum_cons,
        List.map_congr_left hcongr]
      refine add_le_add ?_ ih
      rw [cacheAfter_cons c e es le_rfl]
      have hnil : es.filter (fun f => decide (f.time ≤ e.time)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro f hf
        have h1 := hs.1 f hf
        have h2 : f.time ≠ e.time := fun h => hmem (List.mem_map.2 ⟨f, hf, h⟩)
        simpa using lt_of_le_of_ne h1 (Ne.symm h2)
      have hafter : cacheAfter e.cache es e.time = e.cache := by
        unfold cacheAfter
        rw [hnil, List.map_nil, List.getLastD_nil]
      rw [hafter]
      have hqe : q ∈ e.cache \ c := by
        rw [he]
        simp [hq]
      calc ENNReal.ofReal (minWeight w e.cache) ≤ ENNReal.ofReal (w q) :=
            ENNReal.ofReal_le_ofReal (minWeight_le w _ (Finset.mem_sdiff.1 hqe).1)
        _ ≤ ∑ i ∈ e.cache \ c, ENNReal.ofReal (w i) :=
            Finset.single_le_sum (f := fun i => ENNReal.ofReal (w i)) (fun _ _ => zero_le) hqe

theorem main (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n)
    (w : Fin n → ℝ) (hw : PMDWeights w)
    (O₀ : Finset (Fin n)) (hO₀ : O₀.card = k)
    (σ : Instance n) (hσ : ValidInstance σ) (O : Schedule n)
    (hO : LazyFeasible k O₀ O σ) :
    ENNReal.ofReal (((periodCaches O₀ O).map (minWeight w)).sum) ≤ totalCost w O₀ O σ := by
  obtain ⟨⟨_, _, hsort⟩, hlazy, _⟩ := hO
  calc ENNReal.ofReal (((periodCaches O₀ O).map (minWeight w)).sum)
      ≤ ((((periodCaches O₀ O).map (minWeight w))).map ENNReal.ofReal).sum :=
        ofReal_list_sum_le _
    _ = ((O.map CacheEvent.time).dedup.map
          (fun t => ENNReal.ofReal (minWeight w (cacheAfter O₀ O t)))).sum := by
        simp only [periodCaches, periodTimes, List.map_map]
        rfl
    _ ≤ fetchCostFrom w O₀ O := key w O₀ O hsort hlazy
    _ ≤ totalCost w O₀ O σ := le_self_add

end PagingDelay.PMD.Lemma29

open PagingDelay.PMD in
theorem solution (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n)
    (w : Fin n → ℝ) (hw : PMDWeights w)
    (O₀ : Finset (Fin n)) (hO₀ : O₀.card = k)
    (σ : Instance n) (hσ : ValidInstance σ) (O : Schedule n)
    (hO : LazyFeasible k O₀ O σ) :
    ENNReal.ofReal (((periodCaches O₀ O).map (minWeight w)).sum) ≤ totalCost w O₀ O σ :=
  PagingDelay.PMD.Lemma29.main n k hk hkn w hw O₀ hO₀ σ hσ O hO
