-- Prove2me | solution 1 for PriceOfStability.WeightedSingle.payment_eq_weight_mul_marginalCost
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T17:56:37.681923+00:00
-- url     : https://prove2.me/submissions/1ba173ea-18ff-4ab7-9479-1cebb055ef3c

import Mathlib
import Definitions.Def_PriceOfStability_WeightedSingle_Model
import Definitions.Def_PriceOfStability_WeightedSingle_SingleCommodity

open scoped ENNReal


namespace PriceOfStability.WeightedSingle

section helpers
variable {V ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]

lemma pos_edgeWeight_split (G : WeightedGame ι E) (S : ι → Finset E) (i : ι) (e : E) :
    edgeWeight G S e = (if e ∈ S i then G.weight i else 0) +
      ∑ j ∈ Finset.univ.erase i, (if e ∈ S j then G.weight j else 0) := by
  unfold edgeWeight
  rw [Finset.sum_filter, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]

lemma pos_edgeWeight_update (G : WeightedGame ι E) (S : ι → Finset E) (i : ι) (U : Finset E)
    (e : E) :
    edgeWeight G (Function.update S i U) e + (if e ∈ S i then G.weight i else 0) =
      edgeWeight G S e + (if e ∈ U then G.weight i else 0) := by
  rw [pos_edgeWeight_split G (Function.update S i U) i, pos_edgeWeight_split G S i]
  have : ∑ j ∈ Finset.univ.erase i, (if e ∈ Function.update S i U j then G.weight j else 0)
      = ∑ j ∈ Finset.univ.erase i, (if e ∈ S j then G.weight j else 0) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [this, Function.update_self]
  ring

lemma pos_weight_le_edgeWeight (G : WeightedGame ι E) (hw : ∀ j, 1 ≤ G.weight j)
    (S : ι → Finset E) (i : ι) (e : E) (he : e ∈ S i) :
    G.weight i ≤ edgeWeight G S e := by
  unfold edgeWeight
  exact Finset.single_le_sum (f := G.weight) (fun j _ => by linarith [hw j])
    (Finset.mem_filter.2 ⟨Finset.mem_univ _, he⟩)

lemma pos_edgeWeight_nonneg (G : WeightedGame ι E) (hw : ∀ j, 1 ≤ G.weight j)
    (S : ι → Finset E) (e : E) : 0 ≤ edgeWeight G S e :=
  Finset.sum_nonneg (fun j _ => by linarith [hw j])

lemma pos_payment_nonneg (G : WeightedGame ι E) (hw : ∀ j, 1 ≤ G.weight j)
    (hc : ∀ e, 0 ≤ G.edgeCost e) (S : ι → Finset E) (i : ι) : 0 ≤ payment G S i := by
  unfold payment
  apply Finset.sum_nonneg
  intro e _
  exact mul_nonneg (div_nonneg (by linarith [hw i]) (pos_edgeWeight_nonneg G hw S e)) (hc e)

lemma pos_payment_eq (G : WeightedGame ι E) (hw : ∀ j, 1 ≤ G.weight j)
    (hc : ∀ e, 0 ≤ G.edgeCost e) (S : ι → Finset E) (i : ι) :
    ENNReal.ofReal (payment G S i) = ENNReal.ofReal (G.weight i) * marginalCost G S (S i) := by
  unfold payment marginalCost
  rw [ENNReal.ofReal_sum_of_nonneg, Finset.mul_sum]
  · apply Finset.sum_congr rfl
    intro e he
    have hW : 0 < edgeWeight G S e :=
      lt_of_lt_of_le (by linarith [hw i]) (pos_weight_le_edgeWeight G hw S i e he)
    rw [div_mul_eq_mul_div, ENNReal.ofReal_div_of_pos hW,
      ENNReal.ofReal_mul (by linarith [hw i]), mul_div_assoc]
  · intro e he
    have hW : 0 < edgeWeight G S e :=
      lt_of_lt_of_le (by linarith [hw i]) (pos_weight_le_edgeWeight G hw S i e he)
    exact mul_nonneg (div_nonneg (by linarith [hw i]) hW.le) (hc e)

lemma pos_mc_ne_top (G : WeightedGame ι E) (S : ι → Finset E) (P : Finset E)
    (hP : ∀ e ∈ P, 1 ≤ edgeWeight G S e) : marginalCost G S P ≠ ∞ := by
  unfold marginalCost
  exact ENNReal.sum_ne_top.2 (fun e he => ENNReal.div_ne_top ENNReal.ofReal_ne_top
    (by rw [Ne, ENNReal.ofReal_eq_zero]; linarith [hP e he]))

lemma pos_sum_lt {s : Finset E} {f g : E → ℝ≥0∞} (hle : ∀ x ∈ s, f x ≤ g x) {e : E}
    (he : e ∈ s) (hlt : f e < g e) (hfin : ∑ x ∈ s, f x ≠ ∞) :
    ∑ x ∈ s, f x < ∑ x ∈ s, g x := by
  rw [← Finset.sum_erase_add s f he, ← Finset.sum_erase_add s g he]
  have hfin' : ∑ x ∈ s.erase e, f x ≠ ∞ := by
    rw [← Finset.sum_erase_add s f he] at hfin; exact (ENNReal.add_ne_top.1 hfin).1
  exact ENNReal.add_lt_add_of_le_of_lt hfin'
    (Finset.sum_le_sum fun x hx => hle x (Finset.mem_of_mem_erase hx)) hlt

/-- two simple paths: if one arc list's arcs are among the other's, they coincide -/
lemma pos_list_eq (D : ArcGraph V E) (t : V) :
    ∀ (lP lQ : List E) (v : V),
      lP.IsChain (fun a b => D.tgt a = D.src b) → (lP.map D.src ++ [t]).Nodup →
      lP.head?.map D.src = some v → lP.getLast?.map D.tgt = some t →
      lQ.IsChain (fun a b => D.tgt a = D.src b) → (lQ.map D.src ++ [t]).Nodup →
      lQ.head?.map D.src = some v → lQ.getLast?.map D.tgt = some t →
      (∀ x ∈ lP, x ∈ lQ) → lP = lQ := by
  intro lP
  induction lP with
  | nil => intro lQ v _ _ h; simp at h
  | cons a lP' ih =>
    intro lQ v hcP hnP hhP hlP hcQ hnQ hhQ hlQ hsub
    cases lQ with
    | nil => simp at hhQ
    | cons b lQ' =>
      simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hhP hhQ
      have hab : a = b := by
        have ha := hsub a (by simp)
        rcases List.mem_cons.1 ha with h | h
        · exact h
        · exfalso
          simp only [List.map_cons, List.cons_append, List.nodup_cons, List.mem_append,
            List.mem_map, List.mem_singleton] at hnQ
          exact hnQ.1 (Or.inl ⟨a, h, by rw [hhP, hhQ]⟩)
      subst hab
      congr 1
      cases lP' with
      | nil =>
        cases lQ' with
        | nil => rfl
        | cons c lQ'' =>
          exfalso
          simp only [List.getLast?_singleton, Option.map_some, Option.some.injEq] at hlP
          rw [List.isChain_cons_cons] at hcQ
          simp only [List.map_cons, List.cons_append, List.nodup_cons, List.mem_cons,
            List.mem_append, List.mem_map, List.mem_singleton] at hnQ
          exact hnQ.2.1 (Or.inr (by rw [← hcQ.1, hlP]; simp))
      | cons d lP'' =>
        cases lQ' with
        | nil =>
          exfalso
          simp only [List.getLast?_singleton, Option.map_some, Option.some.injEq] at hlQ
          rw [List.isChain_cons_cons] at hcP
          simp only [List.map_cons, List.cons_append, List.nodup_cons, List.mem_cons,
            List.mem_append, List.mem_map, List.mem_singleton] at hnP
          exact hnP.2.1 (Or.inr (by rw [← hcP.1, hlQ]; simp))
        | cons c lQ'' =>
          rw [List.isChain_cons_cons] at hcP hcQ
          rw [List.getLast?_cons_cons] at hlP hlQ
          have hnP' := hnP
          simp only [List.map_cons, List.cons_append, List.nodup_cons] at hnP hnQ
          apply ih (c :: lQ'') (D.tgt a) hcP.2 (by simpa using hnP.2) (by simp [hcP.1]) hlP
            hcQ.2 (by simpa using hnQ.2) (by simp [hcQ.1]) hlQ
          intro x hx
          have := hsub x (List.mem_cons_of_mem _ hx)
          rcases List.mem_cons.1 this with h | h
          · exfalso
            subst h
            apply hnP.1
            have hm : D.src x ∈ List.map D.src (d :: lP'') := List.mem_map_of_mem hx
            simp only [List.map_cons, List.mem_cons] at hm
            simp only [List.mem_append, List.mem_cons]
            tauto
          · exact h

lemma pos_path_eq (D : ArcGraph V E) (s t : V) (P Q : Finset E)
    (hP : P ∈ stPaths D s t) (hQ : Q ∈ stPaths D s t) (hsub : P ⊆ Q) : P = Q := by
  classical
  simp only [stPaths, Finset.mem_filter] at hP hQ
  obtain ⟨lP, h1, h2, h3, h4, rfl⟩ := hP.2
  obtain ⟨lQ, g1, g2, g3, g4, rfl⟩ := hQ.2
  have := pos_list_eq D t lP lQ s h1 h2 h3 h4 g1 g2 g3 g4
    (fun x hx => List.mem_toFinset.1 (hsub (List.mem_toFinset.2 hx)))
  rw [this]

lemma pos_path_nonempty (D : ArcGraph V E) (s t : V) (P : Finset E)
    (hP : P ∈ stPaths D s t) : P.Nonempty := by
  classical
  simp only [stPaths, Finset.mem_filter] at hP
  obtain ⟨l, h1, h2, h3, h4, rfl⟩ := hP.2
  cases l with
  | nil => simp at h3
  | cons a l => exact ⟨a, by simp⟩

end helpers

section main
variable {V ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]

theorem payment_eq_core (D : ArcGraph V E) (s t : V) (w : ι → ℝ) (c : E → ℝ)
    (hG : (singleCommodityGame D s t w c).IsStandard)
    (S : ι → Finset E) (i : ι) :
    ENNReal.ofReal (payment (singleCommodityGame D s t w c) S i) =
      ENNReal.ofReal (w i) * marginalCost (singleCommodityGame D s t w c) S (S i) :=
  pos_payment_eq _ hG.1 hG.2 S i

/-- the key inequality: after a best-response move the mover's new marginal cost is
strictly below the old marginal cost of every path -/
theorem pos_key (D : ArcGraph V E) (s t : V) (w : ι → ℝ) (c : E → ℝ)
    (hw : ∀ j, 1 ≤ w j) (hc : ∀ e, 0 < c e)
    (S S' : ι → Finset E) (i : ι) (hmove : IsBRMoveBy (singleCommodityGame D s t w c) i S S') :
    ∀ P ∈ stPaths D s t, marginalCost (singleCommodityGame D s t w c) S' (S' i) <
      marginalCost (singleCommodityGame D s t w c) S P := by
  set G := singleCommodityGame D s t w c with hGdef
  have hwG : ∀ j, 1 ≤ G.weight j := hw
  have hcG : ∀ e, 0 ≤ G.edgeCost e := fun e => (hc e).le
  have hcG' : ∀ e, 0 < G.edgeCost e := hc
  obtain ⟨hprof, T, hT, rfl, hlt, hbest⟩ := hmove
  have hw0 : ENNReal.ofReal (G.weight i) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero]; linarith [hwG i]
  have hwt : ENNReal.ofReal (G.weight i) ≠ ∞ := ENNReal.ofReal_ne_top
  have h1 : ∀ U ∈ stPaths D s t, marginalCost G (Function.update S i T) T ≤
      marginalCost G (Function.update S i U) U := by
    intro U hU
    have := ENNReal.ofReal_le_ofReal (hbest U hU)
    rw [pos_payment_eq G hwG hcG, pos_payment_eq G hwG hcG] at this
    simp only [Function.update_self] at this
    exact (ENNReal.mul_le_mul_iff_right hw0 hwt).mp this
  have h2 : marginalCost G (Function.update S i T) T < marginalCost G S (S i) := by
    have h0 := pos_payment_nonneg G hwG hcG (Function.update S i T) i
    have := (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt h0 hlt)).2 hlt
    rw [pos_payment_eq G hwG hcG, pos_payment_eq G hwG hcG] at this
    simp only [Function.update_self] at this
    by_contra hcon
    push_neg at hcon
    have := mul_le_mul_right hcon (ENNReal.ofReal (G.weight i))
    exact absurd this (not_le.2 (by assumption))
  have h3 : ∀ U ∈ stPaths D s t, U ≠ S i →
      marginalCost G (Function.update S i U) U < marginalCost G S U := by
    intro U hU hne
    have hSi : S i ∈ stPaths D s t := hprof i
    obtain ⟨e, heU, heS⟩ : ∃ e ∈ U, e ∉ S i := by
      by_contra hcon
      push_neg at hcon
      exact hne (pos_path_eq D s t U (S i) hU hSi hcon)
    have hWge : ∀ x ∈ U, edgeWeight G S x ≤ edgeWeight G (Function.update S i U) x := by
      intro x hx
      have := pos_edgeWeight_update G S i U x
      rw [if_pos hx] at this
      split_ifs at this <;> linarith [hwG i]
    unfold marginalCost
    apply pos_sum_lt _ heU
    · have hW := pos_edgeWeight_update G S i U e
      rw [if_pos heU, if_neg heS] at hW
      have hW0 := pos_edgeWeight_nonneg G hwG S e
      rcases eq_or_lt_of_le hW0 with h0 | h0
      · rw [← h0, ENNReal.ofReal_zero, ENNReal.div_zero (by
          rw [Ne, ENNReal.ofReal_eq_zero]; linarith [hcG' e])]
        exact lt_top_iff_ne_top.2 (ENNReal.div_ne_top ENNReal.ofReal_ne_top
          (by rw [Ne, ENNReal.ofReal_eq_zero]; linarith [hwG i]))
      · rw [← ENNReal.ofReal_div_of_pos (by linarith [hwG i]),
          ← ENNReal.ofReal_div_of_pos h0]
        rw [ENNReal.ofReal_lt_ofReal_iff (div_pos (hcG' e) h0)]
        exact div_lt_div_of_pos_left (hcG' e) h0 (by linarith [hwG i])
    · have := pos_mc_ne_top G (Function.update S i U) U (fun x hx => by
        have := pos_weight_le_edgeWeight G hwG (Function.update S i U) i x
          (by rw [Function.update_self]; exact hx)
        linarith [hwG i])
      exact this
    · intro x hx
      exact ENNReal.div_le_div_left (ENNReal.ofReal_le_ofReal (hWge x hx)) _
  intro P hP
  simp only [Function.update_self]
  by_cases hPS : P = S i
  · rw [hPS]; exact h2
  · exact lt_of_le_of_lt (h1 P hP) (h3 P hP hPS)

theorem ineq_core (D : ArcGraph V E) (s t : V) (w : ι → ℝ) (c : E → ℝ)
    (hw : ∀ j, 1 ≤ w j) (hc : ∀ e, 0 < c e)
    (S S' : ι → Finset E) (i : ι) (hmove : IsBRMoveBy (singleCommodityGame D s t w c) i S S') :
    (pathsMeeting (stPaths D s t) (S i ∪ S' i)).inf
        (marginalCost (singleCommodityGame D s t w c) S') <
      (pathsMeeting (stPaths D s t) (S i ∪ S' i)).inf
        (marginalCost (singleCommodityGame D s t w c) S) := by
  have hkey := pos_key D s t w c hw hc S S' i hmove
  obtain ⟨hprof, T, hT, hS', -, -⟩ := hmove
  have hT' : S' i = T := by rw [hS', Function.update_self]
  have hmem : S' i ∈ pathsMeeting (stPaths D s t) (S i ∪ S' i) := by
    unfold pathsMeeting
    rw [Finset.mem_filter, hT']
    refine ⟨hT, ?_⟩
    obtain ⟨x, hx⟩ := pos_path_nonempty D s t T hT
    exact ⟨x, by simp [hx]⟩
  obtain ⟨P, hP, hPeq⟩ := Finset.exists_mem_eq_inf _ ⟨_, hmem⟩
    (marginalCost (singleCommodityGame D s t w c) S)
  rw [hPeq]
  refine lt_of_le_of_lt (Finset.inf_le hmem) ?_
  exact hkey P (Finset.mem_filter.1 hP).1

end main

end PriceOfStability.WeightedSingle

open PriceOfStability.WeightedSingle


theorem solution {V ι E : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype E] [DecidableEq E] (D : ArcGraph V E) (s t : V) (w : ι → ℝ) (c : E → ℝ)
    (hG : (singleCommodityGame D s t w c).IsStandard)
    (S : ι → Finset E) (hS : IsProfile (singleCommodityGame D s t w c) S) (i : ι) :
    ENNReal.ofReal (payment (singleCommodityGame D s t w c) S i) =
      ENNReal.ofReal (w i) * marginalCost (singleCommodityGame D s t w c) S (S i) := by
  exact payment_eq_core D s t w c hG S i
