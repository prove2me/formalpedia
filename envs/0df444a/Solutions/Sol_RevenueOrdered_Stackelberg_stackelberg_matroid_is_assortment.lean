-- Prove2me | solution 1 for RevenueOrdered.Stackelberg.stackelberg_matroid_is_assortment
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T00:40:09.377289+00:00
-- url     : https://prove2.me/submissions/2a28bd35-9537-4342-9460-bc1a6eca8877

import Mathlib
import Definitions.Def_RevenueOrdered_Stackelberg_Model
import Definitions.Def_RevenueOrdered_Stackelberg_Greedy
import Definitions.Def_RevenueOrdered_Stackelberg_Instance
import Definitions.Def_RevenueOrdered_Stackelberg_Assortment
import Theorems.Thm_RevenueOrdered_Stackelberg_choiceProb_isRegular
import Theorems.Thm_RevenueOrdered_Stackelberg_revenue_eq_stackRevenue_priceOfAssortment
import Theorems.Thm_RevenueOrdered_Stackelberg_roundUp_revenue_le
import Theorems.Thm_RevenueOrdered_Stackelberg_revenue_assortmentOfPrices_eq

open Classical

namespace StackMainAux

open RevenueOrdered.Stackelberg

variable {α : Type*}

theorem costs_pos (I : Instance α) {q : ℝ} (hq : q ∈ costs I) : 0 < q := by
  unfold costs at hq
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hq
  exact I.cost_pos f hf

theorem abovePrice_gt (I : Instance α) : ∀ f ∈ I.R, I.c f < abovePrice I := by
  intro f hf
  unfold abovePrice
  have : I.c f ≤ ∑ g ∈ I.R, I.c g :=
    Finset.single_le_sum (fun g hg => (I.cost_pos g hg).le) hf
  linarith

theorem abovePrice_pos (I : Instance α) : 0 < abovePrice I := by
  unfold abovePrice
  have : 0 ≤ ∑ g ∈ I.R, I.c g := Finset.sum_nonneg (fun g hg => (I.cost_pos g hg).le)
  linarith

theorem prodRevenue_pos (I : Instance α) (y : Product I) : 0 < prodRevenue I y := by
  have hy := y.2
  unfold products at hy
  rw [Finset.mem_product] at hy
  unfold prodRevenue
  have hB : 0 < (I.B.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨_, hy.1⟩
  exact mul_pos hB (costs_pos I hy.2)

/-- Existence of a customer ordering for any price assignment. -/
theorem exists_customerOrder (I : Instance α) (p : α → ℝ) :
    ∃ L : List α, I.IsCustomerOrder p L := by
  let w := I.weight p
  let r : α → α → Prop := fun e f => w e < w f ∨ (w e = w f ∧ (e ∈ I.R → f ∈ I.R))
  have : Std.Total r := ⟨fun a b => by
    rcases lt_trichotomy (w a) (w b) with h | h | h
    · exact Or.inl (Or.inl h)
    · by_cases ha : a ∈ I.R
      · by_cases hb : b ∈ I.R
        · exact Or.inl (Or.inr ⟨h, fun _ => hb⟩)
        · exact Or.inr (Or.inr ⟨h.symm, fun hb' => absurd hb' hb⟩)
      · exact Or.inl (Or.inr ⟨h, fun ha' => absurd ha' ha⟩)
    · exact Or.inr (Or.inl h)⟩
  have : IsTrans α r := ⟨fun a b c hab hbc => by
    rcases hab with h1 | ⟨h1, h1'⟩ <;> rcases hbc with h2 | ⟨h2, h2'⟩
    · exact Or.inl (h1.trans h2)
    · exact Or.inl (h2 ▸ h1)
    · exact Or.inl (h1 ▸ h2)
    · exact Or.inr ⟨h1.trans h2, fun ha => h2' (h1' ha)⟩⟩
  refine ⟨List.insertionSort r (I.R ∪ I.B).toList, ⟨?_, ?_⟩, ?_⟩
  · exact (List.perm_insertionSort r _).nodup_iff.mpr (Finset.nodup_toList _)
  · ext x
    simp [List.mem_toFinset, (List.perm_insertionSort r _).mem_iff]
  · refine (List.pairwise_insertionSort r _).imp ?_
    intro a b h
    rcases h with h | ⟨h, h'⟩
    · exact ⟨h.le, fun he => absurd he h.ne⟩
    · exact ⟨h.le, fun _ => h'⟩

theorem weight_congr (I : Instance α) (p p' : α → ℝ) (h : ∀ e ∈ I.B, p e = p' e) :
    I.weight p = I.weight p' := by
  funext e
  unfold Instance.weight
  split_ifs with he
  · exact h e he
  · rfl

theorem isCustomerOrder_congr (I : Instance α) (p p' : α → ℝ) (h : ∀ e ∈ I.B, p e = p' e)
    (L : List α) : I.IsCustomerOrder p L ↔ I.IsCustomerOrder p' L := by
  unfold Instance.IsCustomerOrder
  rw [weight_congr I p p' h]

theorem stackRevenue_congr (I : Instance α) (p p' : α → ℝ) (h : ∀ e ∈ I.B, p e = p' e)
    (L : List α) : I.stackRevenue p L = I.stackRevenue p' L := by
  unfold Instance.stackRevenue
  refine Finset.sum_congr rfl ?_
  intro e he
  exact h e (Finset.mem_inter.mp he).1

theorem priceOfAssortment_pos (I : Instance α) (S : Finset (Product I)) (e : α) :
    0 < priceOfAssortment I S e := by
  unfold priceOfAssortment
  simp only
  split_ifs with h
  · have hm := Finset.min'_mem _ h
    obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hm
    rw [← hy]
    have hy2 := y.2
    unfold products at hy2
    exact costs_pos I (Finset.mem_product.mp hy2).2
  · exact abovePrice_pos I

/-- On a threshold set, the induced price is the threshold level on every blue element. -/
theorem priceOfAssortment_thresholdSet (I : Instance α) (y : Product I) (e : α) (he : e ∈ I.B) :
    priceOfAssortment I (thresholdSet (prodRevenue I) y) e = y.1.2 := by
  have hy := y.2
  unfold products at hy
  rw [Finset.mem_product] at hy
  have hB : 0 < (I.B.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨_, hy.1⟩
  have hmem : (e, y.1.2) ∈ products I := by
    unfold products; exact Finset.mem_product.mpr ⟨he, hy.2⟩
  unfold priceOfAssortment
  simp only
  set Q := ((thresholdSet (prodRevenue I) y).filter (fun z => z.1.1 = e)).image
    (fun z => z.1.2) with hQ
  have hq0 : y.1.2 ∈ Q := by
    rw [hQ, Finset.mem_image]
    refine ⟨⟨(e, y.1.2), hmem⟩, ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨?_, rfl⟩
    unfold thresholdSet
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, le_refl _⟩
  have hne : Q.Nonempty := ⟨_, hq0⟩
  rw [dif_pos hne]
  apply le_antisymm
  · exact Finset.min'_le _ _ hq0
  · apply Finset.le_min'
    intro q hq
    rw [hQ, Finset.mem_image] at hq
    obtain ⟨z, hz, rfl⟩ := hq
    rw [Finset.mem_filter] at hz
    have hz1 := hz.1
    unfold thresholdSet at hz1
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz1
    unfold prodRevenue at hz1
    exact le_of_mul_le_mul_left hz1 hB

theorem threshold_eq (I : Instance α) (L : List (α ⊕ (α × ℝ))) (hL : IsAuxOrder I L)
    (y : Product I) (L' : List α) (hL' : I.IsCustomerOrder (fun _ => y.1.2) L') :
    RevenueOrdered.Ratio.revenue (choiceProb I L) (prodRevenue I) (thresholdSet (prodRevenue I) y) =
      I.stackRevenue (fun _ => y.1.2) L' := by
  have hagree : ∀ e ∈ I.B, priceOfAssortment I (thresholdSet (prodRevenue I) y) e =
      (fun _ => y.1.2) e := fun e he => priceOfAssortment_thresholdSet I y e he
  rw [revenue_eq_stackRevenue_priceOfAssortment I L hL _ L'
    ((isCustomerOrder_congr I _ _ hagree L').mpr hL')]
  exact stackRevenue_congr I _ _ hagree L'

end StackMainAux

open RevenueOrdered.Stackelberg StackMainAux in
theorem solution {α : Type*} (I : Instance α) (hB : I.B.Nonempty)
    (L : List (α ⊕ (α × ℝ))) (hL : IsAuxOrder I L) :
    (RevenueOrdered.Ratio.IsRegular (choiceProb I L) ∧ ∀ y : Product I, 0 < prodRevenue I y) ∧
    IsGreatest {v : ℝ | ∃ p : α → ℝ, (∀ e ∈ I.B, 0 < p e) ∧
        ∃ L' : List α, I.IsCustomerOrder p L' ∧ v = I.stackRevenue p L'}
      (RevenueOrdered.Ratio.opt (choiceProb I L) (prodRevenue I)) ∧
    (∀ q ∈ costs I, ∃ y : Product I, ∀ L' : List α, I.IsCustomerOrder (fun _ => q) L' →
        RevenueOrdered.Ratio.revenue (choiceProb I L) (prodRevenue I) (thresholdSet (prodRevenue I) y) =
          I.stackRevenue (fun _ => q) L') ∧
    (∀ y : Product I, ∃ q ∈ costs I, ∀ L' : List α, I.IsCustomerOrder (fun _ => q) L' →
        RevenueOrdered.Ratio.revenue (choiceProb I L) (prodRevenue I) (thresholdSet (prodRevenue I) y) =
          I.stackRevenue (fun _ => q) L') := by
  refine ⟨⟨choiceProb_isRegular I L hL, prodRevenue_pos I⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · -- OPT is attained by some assortment, whose induced price achieves it
    obtain ⟨S, -, hS⟩ := Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset (Finset (Product I))))
      Finset.univ_nonempty (RevenueOrdered.Ratio.revenue (choiceProb I L) (prodRevenue I))
    obtain ⟨L', hL'⟩ := exists_customerOrder I (priceOfAssortment I S)
    refine ⟨priceOfAssortment I S, fun e _ => priceOfAssortment_pos I S e, L', hL', ?_⟩
    unfold RevenueOrdered.Ratio.opt
    rw [hS]
    exact revenue_eq_stackRevenue_priceOfAssortment I L hL S L' hL'
  · rintro v ⟨p, hp, L', hL', rfl⟩
    obtain ⟨hL'r, hle⟩ := roundUp_revenue_le I p hp L' hL'
    have hpos : ∀ e ∈ I.B, 0 < roundUp I p e := by
      intro e _
      unfold roundUp
      split_ifs with h
      · exact costs_pos I (Finset.mem_filter.mp (Finset.min'_mem _ h)).1
      · exact abovePrice_pos I
    have hlev : ∀ e ∈ I.B, roundUp I p e ∈ costs I ∨ ∀ f ∈ I.R, I.c f < roundUp I p e := by
      intro e _
      unfold roundUp
      split_ifs with h
      · exact Or.inl (Finset.mem_filter.mp (Finset.min'_mem _ h)).1
      · exact Or.inr (abovePrice_gt I)
    have heq := revenue_assortmentOfPrices_eq I L hL (roundUp I p) hpos hlev L' hL'r
    refine hle.trans ?_
    rw [← heq]
    unfold RevenueOrdered.Ratio.opt
    exact Finset.le_sup' (RevenueOrdered.Ratio.revenue (choiceProb I L) (prodRevenue I))
      (Finset.mem_univ _)
  · intro q hq
    obtain ⟨e, he⟩ := hB
    have hmem : (e, q) ∈ products I := by
      unfold products; exact Finset.mem_product.mpr ⟨he, hq⟩
    refine ⟨⟨(e, q), hmem⟩, fun L' hL' => ?_⟩
    exact threshold_eq I L hL ⟨(e, q), hmem⟩ L' hL'
  · intro y
    have hy := y.2
    unfold products at hy
    refine ⟨y.1.2, (Finset.mem_product.mp hy).2, fun L' hL' => ?_⟩
    exact threshold_eq I L hL y L' hL'
