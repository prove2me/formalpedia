-- Prove2me | solution 1 for PriceOfStability.WeightedSingle.theorem6_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T18:01:09.236612+00:00
-- url     : https://prove2.me/submissions/d60ce577-ad67-49ed-a91c-0ceda9938a1d

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

theorem lex_core (D : ArcGraph V E) (s t : V) (w : ι → ℝ) (c : E → ℝ)
    (hw : ∀ j, 1 ≤ w j) (hc : ∀ e, 0 < c e)
    (S S' : ι → Finset E) (hmove : IsBRMove (singleCommodityGame D s t w c) S S') :
    List.Lex (· < ·) (sortedCosts (singleCommodityGame D s t w c) (stPaths D s t) S')
      (sortedCosts (singleCommodityGame D s t w c) (stPaths D s t) S) := by
  obtain ⟨i, hmove⟩ := hmove
  have hkey := pos_key D s t w c hw hc S S' i hmove
  obtain ⟨hprof, T, hT, hS', -, -⟩ := hmove
  have hT' : S' i ∈ stPaths D s t := by rw [hS', Function.update_self]; exact hT
  set G := singleCommodityGame D s t w c
  set m := marginalCost G S' (S' i)
  have hm1 : m ∈ sortedCosts G (stPaths D s t) S' := by
    unfold sortedCosts
    rw [Multiset.mem_sort]
    exact Multiset.mem_map.2 ⟨S' i, hT', rfl⟩
  have hA : ∀ y ∈ sortedCosts G (stPaths D s t) S, m < y := by
    intro y hy
    unfold sortedCosts at hy
    rw [Multiset.mem_sort] at hy
    obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.1 hy
    exact hkey P hP
  have hsorted := Multiset.pairwise_sort ((stPaths D s t).val.map (marginalCost G S'))
    (· ≤ ·)
  have hnS : sortedCosts G (stPaths D s t) S ≠ [] := by
    intro h
    have : marginalCost G S (S' i) ∈ sortedCosts G (stPaths D s t) S := by
      unfold sortedCosts
      rw [Multiset.mem_sort]
      exact Multiset.mem_map.2 ⟨S' i, hT', rfl⟩
    rw [h] at this; simp at this
  change List.Pairwise (· ≤ ·) (sortedCosts G (stPaths D s t) S') at hsorted
  revert hm1 hsorted hA hnS
  generalize sortedCosts G (stPaths D s t) S' = l1
  generalize sortedCosts G (stPaths D s t) S = l2
  intro hm1 hA hnS hsorted
  cases l1 with
  | nil => simp at hm1
  | cons x l1 =>
    cases l2 with
    | nil => exact absurd rfl hnS
    | cons y l2 =>
      apply List.Lex.rel
      have hxm : x ≤ m := by
        rcases List.mem_cons.1 hm1 with h | h
        · rw [h]
        · exact List.rel_of_pairwise_cons hsorted h
      exact lt_of_le_of_lt hxm (hA y (by simp))

end main

section goal
variable {V ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]

lemma g_mc_filter (G : WeightedGame ι E) (S : ι → Finset E) (P : Finset E) :
    marginalCost G S P = marginalCost G S (P.filter (fun e => 0 < G.edgeCost e)) := by
  unfold marginalCost
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs with h
  · rfl
  · rw [ENNReal.ofReal_of_nonpos (not_lt.1 h), ENNReal.zero_div]

lemma g_join_le (G : WeightedGame ι E) (hw : ∀ j, 1 ≤ G.weight j)
    (S : ι → Finset E) (i : ι) (U : Finset E) :
    marginalCost G (Function.update S i U) U ≤ marginalCost G S U := by
  unfold marginalCost
  apply Finset.sum_le_sum
  intro x hx
  have := pos_edgeWeight_update G S i U x
  rw [if_pos hx] at this
  have hle : edgeWeight G S x ≤ edgeWeight G (Function.update S i U) x := by
    split_ifs at this <;> linarith [hw i]
  exact ENNReal.div_le_div_left (ENNReal.ofReal_le_ofReal hle) _

lemma g_join_lt (G : WeightedGame ι E) (hw : ∀ j, 1 ≤ G.weight j)
    (S : ι → Finset E) (i : ι) (U : Finset E) (e : E) (heU : e ∈ U) (heS : e ∉ S i)
    (hce : 0 < G.edgeCost e) :
    marginalCost G (Function.update S i U) U < marginalCost G S U := by
  have hWge : ∀ x ∈ U, edgeWeight G S x ≤ edgeWeight G (Function.update S i U) x := by
    intro x hx
    have := pos_edgeWeight_update G S i U x
    rw [if_pos hx] at this
    split_ifs at this <;> linarith [hw i]
  unfold marginalCost
  apply pos_sum_lt _ heU
  · have hW := pos_edgeWeight_update G S i U e
    rw [if_pos heU, if_neg heS] at hW
    have hW0 := pos_edgeWeight_nonneg G hw S e
    rcases eq_or_lt_of_le hW0 with h0 | h0
    · rw [← h0, ENNReal.ofReal_zero, ENNReal.div_zero (by
        rw [Ne, ENNReal.ofReal_eq_zero]; linarith)]
      exact lt_top_iff_ne_top.2 (ENNReal.div_ne_top ENNReal.ofReal_ne_top
        (by rw [Ne, ENNReal.ofReal_eq_zero]; linarith [hw i]))
    · rw [← ENNReal.ofReal_div_of_pos (by linarith [hw i]),
        ← ENNReal.ofReal_div_of_pos h0]
      rw [ENNReal.ofReal_lt_ofReal_iff (div_pos hce h0)]
      exact div_lt_div_of_pos_left hce h0 (by linarith [hw i])
  · exact pos_mc_ne_top G (Function.update S i U) U (fun x hx => by
      have := pos_weight_le_edgeWeight G hw (Function.update S i U) i x
        (by rw [Function.update_self]; exact hx)
      linarith [hw i])
  · intro x hx
    exact ENNReal.div_le_div_left (ENNReal.ofReal_le_ofReal (hWge x hx)) _

lemma g_br_le (G : WeightedGame ι E) (hw : ∀ j, 1 ≤ G.weight j)
    (hc : ∀ e, 0 ≤ G.edgeCost e) (S S' : ι → Finset E) (i : ι) (hmove : IsBRMoveBy G i S S') :
    ∀ U ∈ G.strategies i, marginalCost G S' (S' i) ≤
      marginalCost G (Function.update S i U) U := by
  obtain ⟨hprof, T, hT, rfl, hlt, hbest⟩ := hmove
  have hw0 : ENNReal.ofReal (G.weight i) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero]; linarith [hw i]
  have hwt : ENNReal.ofReal (G.weight i) ≠ ∞ := ENNReal.ofReal_ne_top
  intro U hU
  have := ENNReal.ofReal_le_ofReal (hbest U hU)
  rw [pos_payment_eq G hw hc, pos_payment_eq G hw hc] at this
  simp only [Function.update_self] at this ⊢
  exact (ENNReal.mul_le_mul_iff_right hw0 hwt).mp this

lemma g_br_lt (G : WeightedGame ι E) (hw : ∀ j, 1 ≤ G.weight j)
    (hc : ∀ e, 0 ≤ G.edgeCost e) (S S' : ι → Finset E) (i : ι) (hmove : IsBRMoveBy G i S S') :
    marginalCost G S' (S' i) < marginalCost G S (S i) := by
  obtain ⟨hprof, T, hT, rfl, hlt, hbest⟩ := hmove
  have h0 := pos_payment_nonneg G hw hc (Function.update S i T) i
  have := (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt h0 hlt)).2 hlt
  rw [pos_payment_eq G hw hc, pos_payment_eq G hw hc] at this
  simp only [Function.update_self] at this ⊢
  by_contra hcon
  have hcon' := not_lt.1 hcon
  have := mul_le_mul_right hcon' (ENNReal.ofReal (G.weight i))
  exact absurd this (not_le.2 (by assumption))

/-- a best response is minimal: no feasible path has a strictly smaller positive part -/
lemma g_sub_lt (G : WeightedGame ι E) (hw : ∀ j, 1 ≤ G.weight j)
    (S : ι → Finset E) (i : ι) (U T : Finset E)
    (hsub : U.filter (fun e => 0 < G.edgeCost e) ⊂ T.filter (fun e => 0 < G.edgeCost e)) :
    marginalCost G (Function.update S i U) U < marginalCost G (Function.update S i T) T := by
  rw [g_mc_filter G _ U, g_mc_filter G _ T]
  set pU := U.filter (fun e => 0 < G.edgeCost e)
  set pT := T.filter (fun e => 0 < G.edgeCost e)
  have hpT : ∀ x ∈ pT, x ∈ T := fun x hx => (Finset.mem_filter.1 hx).1
  have heq : marginalCost G (Function.update S i U) pU =
      marginalCost G (Function.update S i T) pU := by
    unfold marginalCost
    apply Finset.sum_congr rfl
    intro x hx
    have hxU : x ∈ U := (Finset.mem_filter.1 hx).1
    have hxT : x ∈ T := hpT x (hsub.1 hx)
    have h1 := pos_edgeWeight_update G S i U x
    have h2 := pos_edgeWeight_update G S i T x
    rw [if_pos hxU] at h1
    rw [if_pos hxT] at h2
    have : edgeWeight G (Function.update S i U) x = edgeWeight G (Function.update S i T) x := by
      linarith
    rw [this]
  rw [heq]
  unfold marginalCost
  rw [← Finset.sum_sdiff hsub.1, add_comm]
  apply ENNReal.lt_add_right
  · exact ENNReal.sum_ne_top.2 (fun x hx => ENNReal.div_ne_top ENNReal.ofReal_ne_top (by
      have := pos_weight_le_edgeWeight G hw (Function.update S i T) i x
        (by rw [Function.update_self]; exact hpT x (hsub.1 hx))
      rw [Ne, ENNReal.ofReal_eq_zero]; linarith [hw i]))
  · obtain ⟨e, he⟩ := Finset.sdiff_nonempty.2 hsub.2
    have heT := hpT e (Finset.mem_sdiff.1 he).1
    have hce : 0 < G.edgeCost e := (Finset.mem_filter.1 (Finset.mem_sdiff.1 he).1).2
    have hWe := pos_weight_le_edgeWeight G hw (Function.update S i T) i e
      (by rw [Function.update_self]; exact heT)
    intro h0
    rw [Finset.sum_eq_zero_iff] at h0
    have := h0 e he
    rw [ENNReal.div_eq_zero_iff] at this
    rcases this with h | h
    · rw [ENNReal.ofReal_eq_zero] at h; linarith
    · exact ENNReal.ofReal_ne_top h

/-- non-minimal path -/
def gNM (𝒮 : Finset (Finset E)) (c : E → ℝ) (P : Finset E) : Prop :=
  ∃ U ∈ 𝒮, U.filter (fun e => 0 < c e) ⊂ P.filter (fun e => 0 < c e)

open Classical in
noncomputable def gCount (𝒮 : Finset (Finset E)) (c : E → ℝ) (S : ι → Finset E) : ℕ :=
  (Finset.univ.filter (fun j => gNM 𝒮 c (S j))).card

noncomputable def gPot (D : ArcGraph V E) (s t : V) (w : ι → ℝ) (c : E → ℝ)
    (S : ι → Finset E) : Lex (ℝ≥0∞ × ℕ) :=
  toLex ((stPaths D s t).inf (marginalCost (singleCommodityGame D s t w c) S),
    gCount (stPaths D s t) c S)

lemma g_pot_lt (D : ArcGraph V E) (s t : V) (w : ι → ℝ) (c : E → ℝ)
    (hw : ∀ j, 1 ≤ w j) (hc : ∀ e, 0 ≤ c e) (S S' : ι → Finset E)
    (hmove : IsBRMove (singleCommodityGame D s t w c) S S') :
    gPot D s t w c S' < gPot D s t w c S := by
  classical
  obtain ⟨i, hmove⟩ := hmove
  set G := singleCommodityGame D s t w c with hGdef
  have hwG : ∀ j, 1 ≤ G.weight j := hw
  have hcG : ∀ e, 0 ≤ G.edgeCost e := hc
  have hle := g_br_le G hwG hcG S S' i hmove
  have hlt := g_br_lt G hwG hcG S S' i hmove
  have hprof := hmove.1
  obtain ⟨T, hT, hS', -, -⟩ := hmove.2
  have hT' : S' i = T := by rw [hS', Function.update_self]
  have hSi : S i ∈ stPaths D s t := hprof i
  have hle' : ∀ P ∈ stPaths D s t, marginalCost G S' (S' i) ≤ marginalCost G S P := by
    intro P hP
    by_cases h : P = S i
    · rw [h]; exact hlt.le
    · exact le_trans (hle P hP) (g_join_le G hwG S i P)
  set m := marginalCost G S' (S' i)
  have hΦ' : (stPaths D s t).inf (marginalCost G S') ≤ m :=
    Finset.inf_le (by rw [hT']; exact hT)
  have hΦ : m ≤ (stPaths D s t).inf (marginalCost G S) := Finset.le_inf hle'
  -- the mover ends on a minimal path
  have hnot : ¬ gNM (stPaths D s t) c (S' i) := by
    rintro ⟨U, hU, hsub⟩
    have h1 := hle U hU
    have h2 := g_sub_lt G hwG S i U T (by rw [hT'] at hsub; exact hsub)
    rw [← hS'] at h2
    have h3 : marginalCost G S' (S' i) < marginalCost G S' (S' i) := by
      calc _ ≤ _ := h1
        _ < _ := h2
        _ = _ := by rw [hT']
    exact lt_irrefl _ h3
  unfold gPot
  rw [Prod.Lex.toLex_lt_toLex]
  rcases lt_or_eq_of_le (le_trans hΦ' hΦ) with h | h
  · exact Or.inl h
  · right
    refine ⟨h, ?_⟩
    -- tie case: S i is non-minimal
    have hNM : gNM (stPaths D s t) c (S i) := by
      obtain ⟨P0, hP0, hP0eq⟩ := Finset.exists_mem_eq_inf _ ⟨_, hSi⟩ (marginalCost G S)
      have hP0m : marginalCost G S P0 ≤ m := by rw [← hP0eq, ← h]; exact hΦ'
      have hchain : m ≤ marginalCost G (Function.update S i P0) P0 := hle P0 hP0
      have hsub : ∀ e ∈ P0, 0 < c e → e ∈ S i := by
        intro e he hce
        by_contra hne
        have := g_join_lt G hwG S i P0 e he hne hce
        exact absurd (lt_of_le_of_lt hchain this) (not_lt.2 hP0m)
      refine ⟨P0, hP0, ?_, ?_⟩
      · intro x hx
        rw [Finset.mem_filter] at hx ⊢
        exact ⟨hsub x hx.1 hx.2, hx.2⟩
      · intro hsup
        have heq : P0.filter (fun e => 0 < c e) = (S i).filter (fun e => 0 < c e) :=
          le_antisymm (fun x hx => by
            rw [Finset.mem_filter] at hx ⊢
            exact ⟨hsub x hx.1 hx.2, hx.2⟩) hsup
        have e1 := g_mc_filter G S P0
        have e2 := g_mc_filter G S (S i)
        have : marginalCost G S P0 = marginalCost G S (S i) := by
          rw [e1, e2]; exact congrArg _ heq
        rw [this] at hP0m
        exact absurd (lt_of_le_of_lt hP0m hlt) (lt_irrefl _)
    unfold gCount
    apply Finset.card_lt_card
    refine ⟨?_, ?_⟩
    · intro j hj
      rw [Finset.mem_filter] at hj ⊢
      refine ⟨hj.1, ?_⟩
      by_cases hji : j = i
      · subst hji; exact absurd hj.2 hnot
      · have : S' j = S j := by rw [hS', Function.update_of_ne hji]
        rw [← this]; exact hj.2
    · intro hsup
      have := hsup (Finset.mem_filter.2 ⟨Finset.mem_univ i, hNM⟩)
      exact hnot (Finset.mem_filter.1 this).2

theorem goal_core (D : ArcGraph V E) (s t : V) (w : ι → ℝ) (c : E → ℝ)
    (hG : (singleCommodityGame D s t w c).IsStandard) :
    WellFounded (fun S' S => IsBRMove (singleCommodityGame D s t w c) S S') ∧
    (∀ S, IsProfile (singleCommodityGame D s t w c) S →
      (¬ ∃ S', IsBRMove (singleCommodityGame D s t w c) S S') →
      IsNash (singleCommodityGame D s t w c) S) ∧
    ((stPaths D s t).Nonempty → ∃ S, IsNash (singleCommodityGame D s t w c) S) := by
  classical
  set G := singleCommodityGame D s t w c with hGdef
  have hw : ∀ j, 1 ≤ w j := hG.1
  have hc : ∀ e, 0 ≤ c e := hG.2
  have hWF : WellFounded (fun S' S => IsBRMove G S S') := by
    let r : (ι → Finset E) → (ι → Finset E) → Prop :=
      fun a b => gPot D s t w c a < gPot D s t w c b
    haveI : IsTrans _ r := ⟨fun _ _ _ h1 h2 => lt_trans h1 h2⟩
    haveI : Std.Irrefl r := ⟨fun _ => lt_irrefl _⟩
    have hr : WellFounded r := Finite.wellFounded_of_trans_of_irrefl r
    exact Subrelation.wf (fun {a b} h => g_pot_lt D s t w c hw hc b a h) hr
  have hNash : ∀ S, IsProfile G S → (¬ ∃ S', IsBRMove G S S') → IsNash G S := by
    intro S hS hno
    refine ⟨hS, ?_⟩
    intro i T hT
    by_contra hlt
    push_neg at hlt
    obtain ⟨U, hU, hUmin⟩ := Finset.exists_min_image (G.strategies i)
      (fun U => payment G (Function.update S i U) i) ⟨T, hT⟩
    apply hno
    refine ⟨Function.update S i U, i, hS, U, hU, rfl, ?_, ?_⟩
    · exact lt_of_le_of_lt (hUmin T hT) hlt
    · intro V' hV'
      exact hUmin V' hV'
  refine ⟨hWF, hNash, ?_⟩
  rintro ⟨P0, hP0⟩
  obtain ⟨S, hS, hmin⟩ := hWF.has_min {S | IsProfile G S} ⟨fun _ => P0, fun _ => hP0⟩
  refine ⟨S, hNash S hS ?_⟩
  rintro ⟨S', i, hmv⟩
  apply hmin S' _ ⟨i, hmv⟩
  obtain ⟨-, T, hT, hS', -, -⟩ := hmv
  intro j
  rw [hS']
  by_cases hji : j = i
  · subst hji; rw [Function.update_self]; exact hT
  · rw [Function.update_of_ne hji]; exact hS j

end goal

end PriceOfStability.WeightedSingle

open PriceOfStability.WeightedSingle


theorem solution {V ι E : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype E] [DecidableEq E] (D : ArcGraph V E) (s t : V) (w : ι → ℝ) (c : E → ℝ)
    (hG : (singleCommodityGame D s t w c).IsStandard) :
    WellFounded (fun S' S => IsBRMove (singleCommodityGame D s t w c) S S') ∧
    (∀ S, IsProfile (singleCommodityGame D s t w c) S →
      (¬ ∃ S', IsBRMove (singleCommodityGame D s t w c) S S') →
      IsNash (singleCommodityGame D s t w c) S) ∧
    ((stPaths D s t).Nonempty → ∃ S, IsNash (singleCommodityGame D s t w c) S) := by
  exact goal_core D s t w c hG
