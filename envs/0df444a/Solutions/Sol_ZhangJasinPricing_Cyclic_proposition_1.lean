-- Prove2me | solution 1 for ZhangJasinPricing.Cyclic.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T08:46:55.525255+00:00
-- url     : https://prove2.me/submissions/762fba8c-64cf-4cd0-947d-c71c39c735aa

import Mathlib
import Definitions.Def_ZhangJasinPricing_Cyclic_Analysis

namespace ZJT

def Comp (S T : List ℕ) : Prop := ∀ j, j < min S.length T.length → S[j]? = T[j]?

lemma elem_le_last {S : List ℕ} (hS : S.Pairwise (· ≤ ·)) (hne : S ≠ []) {i : ℕ}
    (hi : i < S.length) : S[i] ≤ S.getLast hne := by
  rw [List.getLast_eq_getElem]
  rcases Nat.lt_or_ge i (S.length - 1) with h | h
  · exact (List.pairwise_iff_getElem.1 hS) i (S.length - 1) hi (by omega) h
  · have : i = S.length - 1 := by omega
    subst this; exact le_rfl

lemma segB {S T : List ℕ} (hS : S.Pairwise (· ≤ ·)) (hT : T.Pairwise (· ≤ ·)) (hne : S ≠ [])
    (hc : Comp S T) {j a z : ℕ} (hj : T[j]? = some a) (hz : T[j+1]? = some z)
    (hae : a < S.getLast hne) : z ≤ S.getLast hne := by
  obtain ⟨hj1, hz1⟩ := List.getElem?_eq_some_iff.1 hz
  obtain ⟨hj0, hj2⟩ := List.getElem?_eq_some_iff.1 hj
  have hn : 0 < S.length := List.length_pos_iff.2 hne
  by_cases h1 : j + 1 < S.length
  · have e1 := hc (j+1) (by omega)
    rw [hz] at e1
    obtain ⟨_, e2⟩ := List.getElem?_eq_some_iff.1 e1
    rw [← e2]
    exact elem_le_last hS hne h1
  · exfalso
    have h4 : S.length - 1 < T.length := by omega
    have e1 : S[S.length - 1] = T[S.length - 1] := by
      have := hc (S.length - 1) (by omega)
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem h4] at this
      exact Option.some.inj this
    rw [List.getLast_eq_getElem] at hae
    rcases Nat.lt_or_ge (S.length - 1) j with h | h
    · have := (List.pairwise_iff_getElem.1 hT) (S.length - 1) j h4 hj0 h
      omega
    · have : j = S.length - 1 := by omega
      subst this
      omega

lemma segA {S : List ℕ} (hS : S.Pairwise (· ≤ ·)) (hne : S ≠ []) :
    ∀ rest : List (List ℕ), (∀ T ∈ rest, T ≠ [] ∧ T.Pairwise (· ≤ ·) ∧ Comp S T) →
    ∀ v a z, rest.flatten[v]? = some a → a < S.getLast hne →
      rest.flatten[v+1]? = some z → z ≤ S.getLast hne := by
  intro rest
  induction rest with
  | nil => intro _ v a z h; simp at h
  | cons T rest ih =>
    intro hall v a z ha hae hz
    obtain ⟨hTne, hTs, hTc⟩ := hall T (by simp)
    rw [List.flatten_cons] at ha hz
    by_cases h1 : v + 1 < T.length
    · rw [List.getElem?_append_left (by omega)] at ha
      rw [List.getElem?_append_left h1] at hz
      exact segB hS hTs hne hTc ha hz hae
    · by_cases h2 : v + 1 = T.length
      · rw [List.getElem?_append_right (by omega)] at hz
        rw [h2, Nat.sub_self] at hz
        cases rest with
        | nil => simp at hz
        | cons T' r =>
          obtain ⟨hT'ne, _, hT'c⟩ := hall T' (by simp)
          rw [List.flatten_cons] at hz
          have hpos : 0 < T'.length := List.length_pos_iff.2 hT'ne
          rw [List.getElem?_append_left hpos] at hz
          have hSpos : 0 < S.length := List.length_pos_iff.2 hne
          have e1 := hT'c 0 (by omega)
          rw [hz] at e1
          obtain ⟨_, e2⟩ := List.getElem?_eq_some_iff.1 e1
          rw [← e2]
          exact elem_le_last hS hne hSpos
      · rw [List.getElem?_append_right (by omega)] at ha
        rw [List.getElem?_append_right (by omega)] at hz
        have : v + 1 - T.length = (v - T.length) + 1 := by omega
        rw [this] at hz
        exact ih (fun T' hT' => hall T' (by simp [hT'])) _ a z ha hae hz

lemma key (segs : List (List ℕ))
    (hall : ∀ s ∈ segs, s ≠ [] ∧ s.Pairwise (· ≤ ·))
    (hcomp : ∀ s ∈ segs, ∀ s' ∈ segs, Comp s s') :
    ∀ u v x y a z, segs.flatten[u]? = some x → segs.flatten[u+1]? = some y → y < x →
      u + 1 ≤ v → segs.flatten[v]? = some a → a < x → segs.flatten[v+1]? = some z → z ≤ x := by
  induction segs with
  | nil => intro u v x y a z h; simp at h
  | cons S rest ih =>
    intro u v x y a z hx hy hyx huv ha hax hz
    obtain ⟨hne, hS⟩ := hall S (by simp)
    rw [List.flatten_cons] at hx hy ha hz
    have hn : 0 < S.length := List.length_pos_iff.2 hne
    by_cases h1 : u + 1 < S.length
    · rw [List.getElem?_append_left (by omega)] at hx
      rw [List.getElem?_append_left h1] at hy
      obtain ⟨_, e1⟩ := List.getElem?_eq_some_iff.1 hx
      obtain ⟨_, e2⟩ := List.getElem?_eq_some_iff.1 hy
      have := (List.pairwise_iff_getElem.1 hS) u (u+1) (by omega) h1 (by omega)
      omega
    · by_cases h2 : u + 1 = S.length
      · have hu : u = S.length - 1 := by omega
        rw [List.getElem?_append_left (by omega)] at hx
        obtain ⟨_, e1⟩ := List.getElem?_eq_some_iff.1 hx
        have hxe : x = S.getLast hne := by
          rw [List.getLast_eq_getElem, ← e1]; subst hu; rfl
        rw [List.getElem?_append_right (by omega)] at ha hz
        have : v + 1 - S.length = (v - S.length) + 1 := by omega
        rw [this] at hz
        rw [hxe] at hax ⊢
        refine segA hS hne rest ?_ _ a z ha hax hz
        intro T hT
        obtain ⟨h1, h2⟩ := hall T (by simp [hT])
        exact ⟨h1, h2, hcomp S (by simp) T (by simp [hT])⟩
      · rw [List.getElem?_append_right (by omega)] at hx hy ha hz
        have e1 : u + 1 - S.length = (u - S.length) + 1 := by omega
        have e2 : v + 1 - S.length = (v - S.length) + 1 := by omega
        rw [e1] at hy
        rw [e2] at hz
        exact ih (fun s hs => hall s (by simp [hs])) (fun s hs s' hs' => hcomp s (by simp [hs]) s' (by simp [hs']))
          (u - S.length) (v - S.length) x y a z hx hy hyx (by omega) ha hax hz


open ZhangJasinPricing.Cyclic

lemma dec_last {w : List ℕ} (hne : w ≠ []) (h : w.Pairwise (· ≤ ·)) :
    ∀ i ∈ w, i ≤ w.getLastD 0 := by
  intro i hi
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hi
  have := elem_le_last h hne hk
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getLast_of_ne_nil hne]
  simpa using this

lemma dec_to_nested {M : ℕ} {w : Word} (h : Decreasing M w) : NestedDecreasing M w := by
  refine ⟨h.1, dec_last h.1.1 h.2, [w], by simp, ?_, ?_⟩
  · intro s hs; simp at hs; subst hs; exact h
  · intro s hs s' hs' j hj
    simp at hs hs'; subst hs; subst hs'; rfl

lemma aux_sup (s : Finset ℕ) (P : ℕ → Prop) (h0 : P 0) (hm : ∀ k ∈ s, P k) : P (s.sup id) := by
  rcases s.eq_empty_or_nonempty with rfl | h
  · simpa using h0
  · obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup s h id
    rw [he]; exact hm i hi

lemma nested_to_threshold (M : ℕ) (p : ℕ → ℝ) (hnn : ∀ i, i < M → 0 ≤ p i)
    (hord : ∀ i j, i < j → j < M → p j < p i) {w : Word} (h : NestedDecreasing M w) :
    ThresholdRegulated M p w := by
  obtain ⟨hw, hlm, segs, hflat, hdec, hcomp⟩ := h
  refine ⟨hw, hlm, ?_⟩
  have hall : ∀ s ∈ segs, s ≠ [] ∧ s.Pairwise (· ≤ ·) := fun s hs => ⟨(hdec s hs).1.1, (hdec s hs).2⟩
  have K := key segs hall (fun s hs s' hs' j hj => hcomp s hs s' hs' j hj)
  rw [hflat] at K
  have hlt : ∀ i (hi : i < w.length), w[i] < M := fun i hi => hw.2 _ (List.getElem_mem hi)
  have wp : ∀ s (h1 : 1 ≤ s) (h2 : s ≤ w.length), wordPrice p w s = p (w[s-1]'(by omega)) := by
    intro s h1 h2
    unfold wordPrice
    rw [if_neg (by omega), List.getElem?_eq_getElem (by omega)]
    rfl
  have plt : ∀ i j, i < M → j < M → p i < p j → j < i := by
    intro i j hi hj h
    by_contra hc
    rcases Nat.lt_or_ge i j with h' | h'
    · have := hord i j h' hj; linarith
    · have : i = j := by omega
      subst this; exact lt_irrefl _ h
  have ple : ∀ i j, i < M → j < M → i ≤ j → p j ≤ p i := by
    intro i j hi hj h
    rcases h.lt_or_eq with h' | h'
    · exact (hord i j h' hj).le
    · rw [h']
  intro t ht
  rw [Finset.mem_Icc] at ht
  have hWt := wp t ht.1 ht.2
  have hnnt : 0 ≤ wordPrice p w t := by
    rw [hWt]; exact hnn _ (hlt _ _)
  by_cases hl1 : wordPrice p w (t-1) < wordPrice p w t
  · have : threshold p w t = t - 1 := by unfold threshold; rw [if_pos hl1]
    rw [this]; exact hl1.le
  · have : threshold p w t = (Finset.filter (fun k => wordPrice p w k < wordPrice p w (k+1) ∧
        wordPrice p w k < wordPrice p w (t-1)) (Finset.Icc 1 (t-2))).sup id := by
      unfold threshold; rw [if_neg hl1]
    rw [this]
    refine aux_sup _ (fun k => wordPrice p w k ≤ wordPrice p w t) ?_ ?_
    · show wordPrice p w 0 ≤ _
      have h0 : wordPrice p w 0 = 0 := by simp [wordPrice]
      rw [h0]; exact hnnt
    · intro k hk
      rw [Finset.mem_filter, Finset.mem_Icc] at hk
      obtain ⟨⟨hk1, hk2⟩, hk3, hk4⟩ := hk
      show wordPrice p w k ≤ wordPrice p w t
      rw [wp k hk1 (by omega)] at hk3 hk4 ⊢
      rw [wp (k+1) (by omega) (by omega)] at hk3
      rw [wp (t-1) (by omega) (by omega)] at hk4
      rw [hWt]
      have hxM := hlt (k-1) (by omega)
      have hyM := hlt (k+1-1) (by omega)
      have hvM := hlt (t-1-1) (by omega)
      have hzM := hlt (t-1) (by omega)
      have h1 := plt _ _ hxM hyM hk3
      have h2 := plt _ _ hxM hvM hk4
      have := K (k-1) (t-2) (w[k-1]) (w[k+1-1]) (w[t-1-1]) (w[t-1])
        (List.getElem?_eq_getElem (by omega)) (by rw [show k - 1 + 1 = k + 1 - 1 by omega]; exact List.getElem?_eq_getElem (by omega))
        h1 (by omega) (by rw [show t - 2 = t - 1 - 1 by omega]; exact List.getElem?_eq_getElem (by omega)) h2
        (by rw [show t - 2 + 1 = t - 1 by omega]; exact List.getElem?_eq_getElem (by omega))
      exact ple _ _ hzM hxM this

end ZJT

open ZhangJasinPricing.Cyclic in
theorem solution {Ω : Type} [MeasurableSpace Ω] (D : Model Ω) :
    ({w | Decreasing D.M w} ⊆ {w | NestedDecreasing D.M w}) ∧
    ({w | NestedDecreasing D.M w} ⊆ {w | ThresholdRegulated D.M D.price w}) := by
  refine ⟨fun w hw => ZJT.dec_to_nested hw, fun w hw => ?_⟩
  exact ZJT.nested_to_threshold D.M D.price (fun i hi => D.price_nonneg i hi)
    (fun i j hij hj => D.price_order i j hij hj) hw
