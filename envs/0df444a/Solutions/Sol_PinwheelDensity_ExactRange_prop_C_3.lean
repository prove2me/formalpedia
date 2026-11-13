-- Prove2me | solution 1 for PinwheelDensity.ExactRange.prop_C_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:51:39.623208+00:00
-- url     : https://prove2.me/submissions/15df8c76-81ff-4f62-b412-bde7d6f5c931

import Mathlib
import Definitions.Def_PinwheelDensity_ExactRange_Schedulable
import Definitions.Def_PinwheelDensity_ExactRange_cellOf
import Definitions.Def_PinwheelDensity_ExactRange_checkRun

section
set_option autoImplicit false

namespace PinwheelDensity.ExactRange.Dev.FoldAux

open PinwheelDensity.ExactRange

/-! ### Counting executions -/

theorem cnt_succ (s : ℕ → Option ℕ) (i t w : ℕ) :
    cnt s i t (w + 1) = cnt s i t w + if s (t + w) = some i then 1 else 0 := by
  unfold cnt
  rw [List.range_succ, List.filter_append]
  by_cases h : s (t + w) = some i <;> simp [h]

theorem cnt_add (s : ℕ → Option ℕ) (i t a b : ℕ) :
    cnt s i t (a + b) = cnt s i t a + cnt s i (t + a) b := by
  induction b with
  | zero => simp [cnt]
  | succ b ih =>
    rw [← add_assoc, cnt_succ, cnt_succ, ih, add_assoc, add_assoc]

theorem cnt_mono_of_imp (s s' : ℕ → Option ℕ) (i i' t w : ℕ)
    (h : ∀ k, k < w → s (t + k) = some i → s' (t + k) = some i') :
    cnt s i t w ≤ cnt s' i' t w := by
  induction w with
  | zero => simp [cnt]
  | succ w ih =>
    rw [cnt_succ, cnt_succ]
    have := ih (fun k hk => h k (by omega))
    by_cases h1 : s (t + w) = some i
    · have h2 := h w (by omega) h1
      simp [h1, h2]; omega
    · simp only [h1, if_false]
      split_ifs <;> omega

theorem cnt_congr (s s' : ℕ → Option ℕ) (i t w : ℕ)
    (h : ∀ k, k < w → (s (t + k) = some i ↔ s' (t + k) = some i)) :
    cnt s i t w = cnt s' i t w :=
  le_antisymm (cnt_mono_of_imp s s' i i t w fun k hk => (h k hk).1)
    (cnt_mono_of_imp s' s i i t w fun k hk => (h k hk).2)

theorem serves_mono {s : ℕ → Option ℕ} {i : ℕ} {a a' : ℚ} (ha : 0 < a) (haa : a ≤ a')
    (h : Serves s i a) : Serves s i a' := by
  intro t w
  refine le_trans (Nat.floor_le_floor ?_) (h t w)
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) ha haa

/-! ### Lemma A.2 / A.3: relabeling, deletion, monotonicity -/

/-- Relabeling, deletion and monotonicity at once (Lemmas A.2 and A.3): if every entry `B[j]`
of `B` is at least the entry `A[σ j]` of a schedulable list `A`, for an index map `σ` that is
injective on the positions of `B`, then `B` is schedulable. -/
theorem RatSchedulable.of_embed {A B : List ℚ} (σ : ℕ → ℕ)
    (hinj : ∀ j k, j < B.length → k < B.length → σ j = σ k → j = k)
    (hle : ∀ j (hj : j < B.length), ∃ a, A[σ j]? = some a ∧ a ≤ B[j])
    (hA : RatSchedulable A) : RatSchedulable B := by
  classical
  obtain ⟨hpos, s, hs⟩ := hA
  have hσ : ∀ j (hj : j < B.length), ∃ h : σ j < A.length, A[σ j] ≤ B[j] := by
    intro j hj
    obtain ⟨a, ha, hab⟩ := hle j hj
    obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.mp ha
    exact ⟨h, hab⟩
  have hApos : ∀ j (hj : j < B.length), 0 < A[σ j]'(hσ j hj).1 :=
    fun j hj => hpos _ (List.getElem_mem _)
  refine ⟨?_, ?_⟩
  · intro b hb
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hb
    exact lt_of_lt_of_le (hApos j hj) (hσ j hj).2
  · let s' : ℕ → Option ℕ := fun t =>
      match s t with
      | none => none
      | some k => if h : ∃ j, j < B.length ∧ σ j = k then some (Classical.choose h) else none
    refine ⟨s', fun j hj => ?_⟩
    have h1 : Serves s (σ j) B[j] :=
      serves_mono (hApos j hj) (hσ j hj).2 (hs (σ j) (hσ j hj).1)
    intro t w
    refine le_trans (h1 t w) (cnt_mono_of_imp s s' _ _ t w fun k _ hk => ?_)
    have hex : ∃ j', j' < B.length ∧ σ j' = σ j := ⟨j, hj, rfl⟩
    have hc := Classical.choose_spec hex
    have := hinj _ _ hc.1 hj hc.2
    simp only [s', hk, dif_pos hex]
    rw [this]

theorem perm_index {α : Type} {A B : List α} (h : A.Perm B) :
    ∃ σ : ℕ → ℕ, (∀ j, j < B.length → σ j < A.length ∧ A[σ j]? = B[j]?) ∧
      ∀ j k, j < B.length → k < B.length → σ j = σ k → j = k := by
  induction h with
  | nil => exact ⟨id, by simp, by simp⟩
  | cons x _ ih =>
    obtain ⟨σ, h1, h2⟩ := ih
    refine ⟨fun j => if j = 0 then 0 else σ (j - 1) + 1, ?_, ?_⟩
    · intro j hj
      cases j with
      | zero => simp
      | succ j =>
        have := h1 j (by simpa using hj)
        simp only [List.length_cons] at hj ⊢
        simp [this.2]; omega
    · intro j k hj hk hjk
      simp only [List.length_cons] at hj hk
      cases j <;> cases k <;> simp at hjk ⊢
      exact h2 _ _ (by omega) (by omega) hjk
  | swap x y l =>
    refine ⟨fun j => if j = 0 then 1 else if j = 1 then 0 else j, ?_, ?_⟩
    · intro j hj
      simp only [List.length_cons] at hj ⊢
      rcases j with _ | _ | j <;> simp
      omega
    · intro j k hj hk hjk
      simp only at hjk
      split_ifs at hjk <;> omega
  | trans _ _ ih1 ih2 =>
    obtain ⟨σ1, a1, b1⟩ := ih1
    obtain ⟨σ2, a2, b2⟩ := ih2
    refine ⟨fun j => σ1 (σ2 j), ?_, ?_⟩
    · intro j hj
      obtain ⟨c1, c2⟩ := a2 j hj
      obtain ⟨d1, d2⟩ := a1 (σ2 j) c1
      exact ⟨d1, d2.trans c2⟩
    · intro j k hj hk h
      exact b2 j k hj hk (b1 _ _ (a2 j hj).1 (a2 k hk).1 h)

/-- Componentwise `≤` as `List.Forall₂`. -/
theorem leAll_iff : ∀ (l m : List ℚ), leAll l m = true ↔ List.Forall₂ (· ≤ ·) l m
  | [], [] => by simp [leAll]
  | [], _ :: _ => by simp [leAll]
  | _ :: _, [] => by simp [leAll]
  | a :: l, b :: m => by simp [leAll, leAll_iff l m]

/-- Lemma A.2: schedulability is invariant under permutations. -/
theorem RatSchedulable.perm {A B : List ℚ} (h : A.Perm B) (hA : RatSchedulable A) :
    RatSchedulable B := by
  obtain ⟨σ, h1, h2⟩ := perm_index h
  refine RatSchedulable.of_embed σ h2 (fun j hj => ?_) hA
  obtain ⟨c1, c2⟩ := h1 j hj
  exact ⟨B[j], by rw [c2]; simp [hj], le_refl _⟩

/-- Lemma A.3: schedulability is monotone in the periods (componentwise). -/
theorem RatSchedulable.mono {A B : List ℚ} (h : List.Forall₂ (· ≤ ·) A B)
    (hA : RatSchedulable A) : RatSchedulable B := by
  obtain ⟨hl, hge⟩ := List.forall₂_iff_get.mp h
  refine RatSchedulable.of_embed id (fun j k _ _ hjk => hjk) (fun j hj => ?_) hA
  have hj' : j < A.length := by omega
  exact ⟨A[j], by simp [hj'], by simpa using hge j hj' hj⟩

/-! ### Lemma A.4: the pair fold -/

theorem half_floor {x m : ℚ} (hm : 0 < m) (hx : 2 * m ≤ x) (w : ℕ) :
    ⌊(w : ℚ) / x⌋₊ ≤ ⌊(w : ℚ) / m⌋₊ / 2 := by
  have h2 := Nat.floor_div_natCast ((w : ℚ) / m) 2
  push_cast at h2
  rw [← h2]
  refine Nat.floor_le_floor ?_
  rw [div_div, div_le_div_iff₀ (by linarith) (by positivity)]
  have : (0 : ℚ) ≤ w := Nat.cast_nonneg _
  nlinarith

/-- Lemma A.4 (pair fold): if `A ++ [min x y / 2]` is schedulable, so is `A ++ [x, y]`. -/
theorem RatSchedulable.pairFold {A : List ℚ} {x y : ℚ} (hx : 0 < x) (hy : 0 < y)
    (h : RatSchedulable (A ++ [min x y / 2])) : RatSchedulable (A ++ [x, y]) := by
  obtain ⟨hpos, s, hs⟩ := h
  have hμ : 0 < min x y / 2 := by have := lt_min hx hy; linarith
  let ν := A.length
  let N : ℕ → ℕ := fun t => cnt s ν 0 t
  let s' : ℕ → Option ℕ := fun t =>
    if s t = some ν then (if N t % 2 = 0 then some ν else some (ν + 1))
    else if s t = some (ν + 1) then none else s t
  have e1 : ∀ t, s' t = some ν ↔ s t = some ν ∧ N t % 2 = 0 := by
    intro t; simp only [s']; split_ifs <;> simp_all
  have e2 : ∀ t, s' t = some (ν + 1) ↔ s t = some ν ∧ ¬ N t % 2 = 0 := by
    intro t; simp only [s']; split_ifs <;> simp_all
  have e3 : ∀ t i, i < ν → (s' t = some i ↔ s t = some i) := by
    intro t i hi; simp only [s']; split_ifs <;> simp_all <;> omega
  have key : ∀ t w, cnt s' ν t w = (cnt s ν t w + (if N t % 2 = 0 then 1 else 0)) / 2 ∧
      cnt s' (ν + 1) t w = (cnt s ν t w + (if N t % 2 = 0 then 0 else 1)) / 2 := by
    intro t w
    induction w with
    | zero => split_ifs <;> simp [cnt]
    | succ w ih =>
      simp only [cnt_succ]
      have hN : N (t + w) = N t + cnt s ν t w := by
        have := cnt_add s ν 0 t w
        simpa [N] using this
      have f1 := e1 (t + w)
      have f2 := e2 (t + w)
      rw [hN] at f1 f2
      obtain ⟨ih1, ih2⟩ := ih
      by_cases hc : s (t + w) = some ν
      · by_cases hp : (N t + cnt s ν t w) % 2 = 0
        · have g1 : s' (t + w) = some ν := f1.2 ⟨hc, hp⟩
          have g2 : ¬ s' (t + w) = some (ν + 1) := fun hh => (f2.1 hh).2 hp
          simp [g1, g2, hc]
          split_ifs at ih1 ih2 ⊢ <;> omega
        · have g1 : ¬ s' (t + w) = some ν := fun hh => hp (f1.1 hh).2
          have g2 : s' (t + w) = some (ν + 1) := f2.2 ⟨hc, hp⟩
          simp [g1, g2, hc]
          split_ifs at ih1 ih2 ⊢ <;> omega
      · have g1 : ¬ s' (t + w) = some ν := fun hh => hc (f1.1 hh).1
        have g2 : ¬ s' (t + w) = some (ν + 1) := fun hh => hc (f2.1 hh).1
        simp [g1, g2, hc]
        split_ifs at ih1 ih2 ⊢ <;> omega
  refine ⟨?_, s', ?_⟩
  · intro a ha
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with ha | rfl | rfl
    · exact hpos a (by simp [ha])
    · exact hx
    · exact hy
  · intro i hi
    simp only [List.length_append, List.length_cons, List.length_nil, ν] at hi
    have hAl : (A ++ [x, y]).length = A.length + 2 := by simp
    rcases Nat.lt_or_ge i A.length with hlt | hge
    · have e : (A ++ [x, y])[i] = (A ++ [min x y / 2])[i]'(by simp; omega) := by
        rw [List.getElem_append_left hlt, List.getElem_append_left hlt]
      intro t w
      rw [e]
      have := hs i (by simp; omega) t w
      rw [cnt_congr s' s i t w (fun k _ => e3 _ i hlt)]
      exact this
    · have hμs : (A ++ [min x y / 2])[ν]'(by simp [ν]) = min x y / 2 := by simp [ν]
      have hs0 := hs ν (by simp [ν])
      rw [hμs] at hs0
      rcases (show i = A.length ∨ i = A.length + 1 by omega) with rfl | rfl
      · have e : (A ++ [x, y])[A.length] = x := by simp
        intro t w
        rw [e]
        have := half_floor (x := x) (m := min x y / 2) hμ (by have := min_le_left x y; linarith) w
        have h3 := hs0 t w
        have h4 := (key t w).1
        rw [h4]
        have : ⌊(w : ℚ) / x⌋₊ ≤ cnt s ν t w / 2 := le_trans this (Nat.div_le_div_right h3)
        omega
      · have e : (A ++ [x, y])[A.length + 1] = y := by simp
        intro t w
        rw [e]
        have := half_floor (x := y) (m := min x y / 2) hμ (by have := min_le_right x y; linarith) w
        have h3 := hs0 t w
        have h4 := (key t w).2
        rw [h4]
        have : ⌊(w : ℚ) / y⌋₊ ≤ cnt s ν t w / 2 := le_trans this (Nat.div_le_div_right h3)
        omega

/-! ### Lemma A.5: sorting is monotone -/

theorem sortQ_perm (l : List ℚ) : (sortQ l).Perm l := List.perm_insertionSort _ l

theorem sortQ_sorted (l : List ℚ) : (sortQ l).Pairwise (· ≤ ·) :=
  List.pairwise_insertionSort _ l

theorem sortQ_cons (a : ℚ) (l : List ℚ) :
    sortQ (a :: l) = List.orderedInsert (· ≤ ·) a (sortQ l) := by
  simp [sortQ]

/-- Sorting only depends on the multiset of entries. -/
theorem sortQ_congr_perm {l l' : List ℚ} (h : l.Perm l') : sortQ l = sortQ l' :=
  List.Perm.eq_of_pairwise (fun _ _ _ _ h1 h2 => le_antisymm h1 h2)
    (sortQ_sorted l) (sortQ_sorted l') ((sortQ_perm l).trans (h.trans (sortQ_perm l').symm))

theorem fle_refl : ∀ l : List ℚ, List.Forall₂ (· ≤ ·) l l := fun l =>
  List.forall₂_same.2 (fun _ _ => le_rfl)

theorem fle_trans {a b c : List ℚ} (h1 : List.Forall₂ (· ≤ ·) a b)
    (h2 : List.Forall₂ (· ≤ ·) b c) : List.Forall₂ (· ≤ ·) a c := by
  induction h1 generalizing c with
  | nil => exact h2
  | cons h t ih =>
    cases h2 with
    | cons h' t' => exact List.Forall₂.cons (le_trans h h') (ih t')

theorem ins_ge {x b : ℚ} {L : List ℚ} (hL : L.Pairwise (· ≤ ·)) (hx : ∀ y ∈ L, x ≤ y)
    (hxb : x ≤ b) :
    List.Forall₂ (· ≤ ·) (x :: L) (List.orderedInsert (· ≤ ·) b L) := by
  induction L generalizing x with
  | nil => simpa using hxb
  | cons y L ih =>
    by_cases h : b ≤ y
    · rw [List.orderedInsert_cons, if_pos h]
      exact List.Forall₂.cons hxb (fle_refl _)
    · rw [List.orderedInsert_cons, if_neg h]
      exact List.Forall₂.cons (hx y (by simp))
        (ih hL.of_cons (fun z hz => List.rel_of_pairwise_cons hL hz) (le_of_not_ge h))

theorem insert_mono {a b : ℚ} (hab : a ≤ b) {L : List ℚ} (hL : L.Pairwise (· ≤ ·)) :
    List.Forall₂ (· ≤ ·) (List.orderedInsert (· ≤ ·) a L) (List.orderedInsert (· ≤ ·) b L) := by
  induction L with
  | nil => simpa using hab
  | cons x L ih =>
    have hxL : ∀ y ∈ L, x ≤ y := fun y hy => List.rel_of_pairwise_cons hL hy
    by_cases h1 : a ≤ x
    · by_cases h2 : b ≤ x
      · rw [List.orderedInsert_cons, List.orderedInsert_cons, if_pos h1, if_pos h2]
        exact List.Forall₂.cons hab (fle_refl _)
      · rw [List.orderedInsert_cons, List.orderedInsert_cons, if_pos h1, if_neg h2]
        exact List.Forall₂.cons h1 (ins_ge hL.of_cons hxL (le_of_not_ge h2))
    · have h2 : ¬ b ≤ x := fun h => h1 (le_trans hab h)
      rw [List.orderedInsert_cons, List.orderedInsert_cons, if_neg h1, if_neg h2]
      exact List.Forall₂.cons le_rfl (ih hL.of_cons)

/-- Changing one entry upward changes the sorted list upward. -/
theorem sortQ_single {a b : ℚ} (hab : a ≤ b) (l1 l2 : List ℚ) :
    List.Forall₂ (· ≤ ·) (sortQ (l1 ++ a :: l2)) (sortQ (l1 ++ b :: l2)) := by
  rw [sortQ_congr_perm (List.perm_middle), sortQ_congr_perm (List.perm_middle), sortQ_cons,
    sortQ_cons]
  exact insert_mono hab (sortQ_sorted _)

/-- Lemma A.5: if `r ≤ s` componentwise, then `sort r ≤ sort s` componentwise. -/
theorem sortQ_mono {r s : List ℚ} (h : List.Forall₂ (· ≤ ·) r s) :
    List.Forall₂ (· ≤ ·) (sortQ r) (sortQ s) := by
  have key : Relation.ReflTransGen
      (fun u v : List ℚ => ∃ l1 l2 a b, a ≤ b ∧ u = l1 ++ a :: l2 ∧ v = l1 ++ b :: l2) r s := by
    induction h with
    | nil => exact Relation.ReflTransGen.refl
    | @cons a b l1 l2 hab _ ih =>
      refine Relation.ReflTransGen.trans (b := b :: l1) ?_ ?_
      · exact Relation.ReflTransGen.single ⟨[], l1, a, b, hab, rfl, rfl⟩
      · refine Relation.ReflTransGen.lift (b :: ·) ?_ _ _ ih
        rintro u v ⟨m1, m2, c, d, hcd, rfl, rfl⟩
        exact ⟨b :: m1, m2, c, d, hcd, rfl, rfl⟩
  clear h
  induction key with
  | refl => exact fle_refl _
  | tail _ hst ih =>
    obtain ⟨l1, l2, a, b, hab, rfl, rfl⟩ := hst
    exact fle_trans ih (sortQ_single hab l1 l2)

/-! ### Lemma A.6: folding preserves order -/

theorem fle_eraseIdx {l1 l2 : List ℚ} (h : List.Forall₂ (· ≤ ·) l1 l2) (k : ℕ) :
    List.Forall₂ (· ≤ ·) (l1.eraseIdx k) (l2.eraseIdx k) := by
  induction h generalizing k with
  | nil => simp
  | cons hab _ ih =>
    cases k with
    | zero => simpa using ‹List.Forall₂ _ _ _›
    | succ k => simpa using List.Forall₂.cons hab (ih k)

theorem fle_getElem? {r s : List ℚ} (h : List.Forall₂ (· ≤ ·) r s) {i : ℕ} {a : ℚ}
    (ha : r[i]? = some a) : ∃ a', s[i]? = some a' ∧ a ≤ a' := by
  obtain ⟨hl, hge⟩ := List.forall₂_iff_get.mp h
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp ha
  exact ⟨s[i]'(by omega), by simp [show i < s.length by omega], by simpa using hge i hi (by omega)⟩

/-- Lemma A.6 (one fold): `fold_ij` preserves componentwise order. -/
theorem pairFold_mono {r s r' : List ℚ} (h : List.Forall₂ (· ≤ ·) r s) {i j : ℕ}
    (hr : pairFold r i j = some r') :
    ∃ s', pairFold s i j = some s' ∧ List.Forall₂ (· ≤ ·) r' s' := by
  unfold pairFold at hr ⊢
  by_cases hij : i = j
  · simp [hij] at hr
  · rw [if_neg hij] at hr ⊢
    cases hi : r[i]? with
    | none => simp [hi] at hr
    | some a =>
      cases hj : r[j]? with
      | none => simp [hi, hj] at hr
      | some b =>
        obtain ⟨a', hi', haa⟩ := fle_getElem? h hi
        obtain ⟨b', hj', hbb⟩ := fle_getElem? h hj
        simp only [hi, hj, Option.some.injEq] at hr
        simp only [hi', hj']
        refine ⟨_, rfl, ?_⟩
        rw [← hr]
        refine sortQ_mono (List.rel_append (fle_eraseIdx (fle_eraseIdx h _) _) ?_)
        exact List.Forall₂.cons
          (div_le_div_of_nonneg_right (min_le_min haa hbb) (by norm_num)) List.Forall₂.nil

/-- Lemma A.6: `π(r) ≤ π(s)` componentwise whenever `r ≤ s` and `π(r)` is defined. -/
theorem applyPairs_mono {r s r' : List ℚ} (h : List.Forall₂ (· ≤ ·) r s)
    (π : List (ℕ × ℕ)) (hr : applyPairs π r = some r') :
    ∃ s', applyPairs π s = some s' ∧ List.Forall₂ (· ≤ ·) r' s' := by
  induction π generalizing r s with
  | nil =>
    simp only [applyPairs, Option.some.injEq] at hr
    subst hr; exact ⟨s, rfl, h⟩
  | cons p π ih =>
    obtain ⟨i, j⟩ := p
    simp only [applyPairs] at hr
    cases hf : pairFold r i j with
    | none => simp [hf] at hr
    | some r1 =>
      rw [hf] at hr
      obtain ⟨s1, hs1, h1⟩ := pairFold_mono h hf
      obtain ⟨s', hs', h'⟩ := ih h1 hr
      exact ⟨s', by simp [applyPairs, hs1, hs'], h'⟩

/-! ### Corollary A.7: domination certificates -/

theorem perm_pair (v : List ℚ) {p q : ℕ} (hpq : p < q) (hq : q < v.length) :
    v.Perm (v[q] :: v[p]'(by omega) :: ((v.eraseIdx q).eraseIdx p)) := by
  have h1 := (List.getElem_cons_eraseIdx_perm hq).symm
  have hp : p < (v.eraseIdx q).length := by rw [List.length_eraseIdx_of_lt hq]; omega
  have h2 := (List.getElem_cons_eraseIdx_perm hp).symm
  rw [List.getElem_eraseIdx_of_lt hp hpq] at h2
  exact h1.trans (h2.cons _)

theorem pos_of_min_half {x y : ℚ} (h : 0 < min x y / 2) : 0 < x ∧ 0 < y := by
  have : 0 < min x y := by linarith
  exact lt_min_iff.mp this

theorem pairFold_sound_aux (v : List ℚ) {p q : ℕ} (hpq : p < q) (hq : q < v.length)
    (hs : RatSchedulable ((v.eraseIdx q).eraseIdx p ++ [min v[q] (v[p]'(by omega)) / 2])) :
    RatSchedulable v := by
  obtain ⟨hx, hy⟩ := pos_of_min_half (hs.1 (min v[q] (v[p]'(by omega)) / 2) (by simp))
  have h := RatSchedulable.pairFold hx hy hs
  refine RatSchedulable.perm ?_ h
  refine (List.perm_append_comm.trans ?_)
  exact (perm_pair v hpq hq).symm

/-- One fold can be undone (Lemmas A.4 and A.2): if `fold_ij(v)` is schedulable, so is `v`. -/
theorem pairFold_sound {v v' : List ℚ} {i j : ℕ} (h : pairFold v i j = some v')
    (hs : RatSchedulable v') : RatSchedulable v := by
  unfold pairFold at h
  by_cases hij : i = j
  · simp [hij] at h
  · rw [if_neg hij] at h
    cases hi : v[i]? with
    | none => simp [hi] at h
    | some a =>
      cases hj : v[j]? with
      | none => simp [hi, hj] at h
      | some b =>
        simp only [hi, hj, Option.some.injEq] at h
        subst h
        obtain ⟨hi', rfl⟩ := List.getElem?_eq_some_iff.mp hi
        obtain ⟨hj', rfl⟩ := List.getElem?_eq_some_iff.mp hj
        have hs1 := RatSchedulable.perm (sortQ_perm _) hs
        rcases lt_or_gt_of_ne hij with h | h
        · rw [max_eq_right h.le, min_eq_left h.le] at hs1
          rw [min_comm] at hs1
          exact pairFold_sound_aux v h hj' hs1
        · rw [max_eq_left h.le, min_eq_right h.le] at hs1
          exact pairFold_sound_aux v h hi' hs1

/-- Undoing a whole sequence of folds: if `π(v)` is defined and schedulable, so is `v`. -/
theorem applyPairs_sound {v w : List ℚ} (π : List (ℕ × ℕ)) (h : applyPairs π v = some w)
    (hs : RatSchedulable w) : RatSchedulable v := by
  induction π generalizing v with
  | nil =>
    simp only [applyPairs, Option.some.injEq] at h
    subst h; exact hs
  | cons p π ih =>
    obtain ⟨i, j⟩ := p
    simp only [applyPairs] at h
    cases hf : pairFold v i j with
    | none => simp [hf] at h
    | some v1 =>
      rw [hf] at h
      exact pairFold_sound hf (ih h)

/-- Corollary A.7 (domination certificates), stated for an arbitrary list `b` (sortedness is
not needed): if `L ≤ b` componentwise, `π(sort L)` is defined and `sort r ≤ π(sort L)`
componentwise for a schedulable `r`, then `b` is schedulable. -/
theorem dominated_sound {b L r v : List ℚ} {π : List (ℕ × ℕ)}
    (hL : List.Forall₂ (· ≤ ·) L b) (hπ : applyPairs π (sortQ L) = some v)
    (hr : RatSchedulable r) (hle : leAll (sortQ r) v = true) : RatSchedulable b := by
  have h1 := sortQ_mono hL
  obtain ⟨w, hw, hvw⟩ := applyPairs_mono h1 π hπ
  have h2 : List.Forall₂ (· ≤ ·) (sortQ r) w := fle_trans ((leAll_iff _ _).1 hle) hvw
  have h3 : RatSchedulable (sortQ b) :=
    applyPairs_sound π hw (RatSchedulable.mono h2 (RatSchedulable.perm (sortQ_perm r).symm hr))
  exact RatSchedulable.perm (sortQ_perm b) h3

end PinwheelDensity.ExactRange.Dev.FoldAux
end

section
set_option autoImplicit false

namespace PinwheelDensity.ExactRange.Dev.LC3

open PinwheelDensity.ExactRange PinwheelDensity.ExactRange.Dev.FoldAux

/-- The schedule defined by a cyclic word. -/
def sch (w : List ℕ) : ℕ → Option ℕ := fun t => w[t % w.length]?

/-- The extended occurrence function `T(j) = t_{j mod n} + ⌊j/n⌋ N`. -/
def TT (w : List ℕ) (i j : ℕ) : ℕ :=
  (occurrences w i).getD (j % (occurrences w i).length) 0 +
    (j / (occurrences w i).length) * w.length

theorem mem_occ (w : List ℕ) (i x : ℕ) :
    x ∈ occurrences w i ↔ x < w.length ∧ w[x]? = some i := by
  simp [occurrences, List.mem_filter, List.mem_range]

theorem occ_pw (w : List ℕ) (i : ℕ) : (occurrences w i).Pairwise (· < ·) := by
  unfold occurrences
  exact List.Pairwise.filter _ (List.pairwise_lt_range)

theorem occ_lt (w : List ℕ) (i k : ℕ) (hk : k < (occurrences w i).length) :
    (occurrences w i).getD k 0 < w.length := by
  rw [List.getD_eq_getElem _ _ hk]
  exact ((mem_occ w i _).1 (List.getElem_mem hk)).1

theorem occ_mono (w : List ℕ) (i a b : ℕ) (hab : a < b) (hb : b < (occurrences w i).length) :
    (occurrences w i).getD a 0 < (occurrences w i).getD b 0 := by
  have ha : a < (occurrences w i).length := by omega
  rw [List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ hb]
  exact List.pairwise_iff_getElem.1 (occ_pw w i) a b ha hb hab

theorem TT_strict (w : List ℕ) (i : ℕ) (hn : 0 < (occurrences w i).length) {j k : ℕ}
    (hjk : j < k) : TT w i j < TT w i k := by
  unfold TT
  set n := (occurrences w i).length with hn'
  have h1 := occ_lt w i (j % n) (Nat.mod_lt _ hn)
  have h2 := occ_lt w i (k % n) (Nat.mod_lt _ hn)
  rcases Nat.lt_or_ge (j / n) (k / n) with h | h
  · have : (j / n + 1) * w.length ≤ (k / n) * w.length := Nat.mul_le_mul_right _ h
    nlinarith
  · have hjn : j / n = k / n := by
      have : j / n ≤ k / n := Nat.div_le_div_right hjk.le
      omega
    have hm : j % n < k % n := by
      have e1 := Nat.mod_add_div j n
      have e2 := Nat.mod_add_div k n
      rw [hjn] at e1
      have : n * (k / n) = n * (k / n) := rfl
      nlinarith
    have := occ_mono w i _ _ hm (Nat.mod_lt _ hn)
    rw [hjn]; omega

theorem TT_add (w : List ℕ) (i : ℕ) (hn : 0 < (occurrences w i).length) (j : ℕ) :
    TT w i (j + (occurrences w i).length) = TT w i j + w.length := by
  unfold TT
  set n := (occurrences w i).length
  rw [Nat.add_mod_right, Nat.add_div_right _ hn]
  ring

theorem TT_ext (w : List ℕ) (i k : ℕ) (hk : k < 2 * (occurrences w i).length)
    (hn : 0 < (occurrences w i).length) : TT w i k = extOcc w i k := by
  unfold TT extOcc
  simp only
  set n := (occurrences w i).length
  by_cases h : k < n
  · rw [if_pos h, Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h]; simp
  · rw [if_neg h]
    have : k = (k - n) + n := by omega
    have e : TT w i k = TT w i (k - n) + w.length := by
      conv_lhs => rw [this]
      exact TT_add w i hn _
    unfold TT at e
    rw [e, Nat.mod_eq_of_lt (by omega : k - n < n), Nat.div_eq_of_lt (by omega : k - n < n)]
    simp

theorem sch_iff (w : List ℕ) (i : ℕ) (hN : 0 < w.length) (x : ℕ) :
    sch w x = some i ↔ ∃ j, TT w i j = x ∧ 0 < (occurrences w i).length := by
  constructor
  · intro h
    have hx : x % w.length ∈ occurrences w i :=
      (mem_occ w i _).2 ⟨Nat.mod_lt _ hN, h⟩
    obtain ⟨m, hm, hmx⟩ := List.mem_iff_getElem.1 hx
    have hn : 0 < (occurrences w i).length := by omega
    refine ⟨m + (x / w.length) * (occurrences w i).length, ?_, hn⟩
    unfold TT
    set n := (occurrences w i).length
    have e1 : (m + x / w.length * n) % n = m := by
      rw [Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt hm
    have e2 : (m + x / w.length * n) / n = x / w.length := by
      rw [Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hm]; simp
    rw [e1, e2, List.getD_eq_getElem _ _ hm, hmx]
    rw [mul_comm]; exact Nat.mod_add_div x w.length
  · rintro ⟨j, rfl, hn⟩
    have h1 := occ_lt w i (j % (occurrences w i).length) (Nat.mod_lt _ hn)
    have hmem : (occurrences w i).getD (j % (occurrences w i).length) 0 ∈ occurrences w i := by
      rw [List.getD_eq_getElem _ _ (Nat.mod_lt _ hn)]; exact List.getElem_mem _
    have := ((mem_occ w i _).1 hmem).2
    unfold sch TT
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h1]
    exact this


/-- The prefix count `F x`. -/
theorem F_spec (w : List ℕ) (i : ℕ) (hN : 0 < w.length) (hn : 0 < (occurrences w i).length)
    (x : ℕ) :
    x ≤ TT w i (cnt (sch w) i 0 x) ∧
      (0 < cnt (sch w) i 0 x → TT w i (cnt (sch w) i 0 x - 1) < x) := by
  induction x with
  | zero => simp [cnt]
  | succ x ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [cnt_succ]
    simp only [zero_add]
    by_cases h : sch w x = some i
    · obtain ⟨j, hj, -⟩ := (sch_iff w i hN x).1 h
      rw [if_pos h]
      have hjF : j = cnt (sch w) i 0 x := by
        have a1 : j ≤ cnt (sch w) i 0 x := by
          by_contra hc
          have := TT_strict w i hn (not_le.1 hc)
          omega
        have a2 : cnt (sch w) i 0 x ≤ j := by
          by_cases hz : 0 < cnt (sch w) i 0 x
          · by_contra hc
            have hle : j ≤ cnt (sch w) i 0 x - 1 := by omega
            have := h2 hz
            rcases hle.eq_or_lt with e | e
            · rw [e] at hj; omega
            · have := TT_strict w i hn e; omega
          · omega
        omega
      subst hjF
      refine ⟨?_, fun _ => ?_⟩
      · have := TT_strict w i hn (show cnt (sch w) i 0 x < cnt (sch w) i 0 x + 1 by omega); omega
      · simp only [Nat.add_sub_cancel]; omega
    · rw [if_neg h]
      refine ⟨?_, fun hp => ?_⟩
      · have : TT w i (cnt (sch w) i 0 x) ≠ x := by
          intro he; exact h ((sch_iff w i hN x).2 ⟨_, he, hn⟩)
        simp only [add_zero]
        omega
      · simp only [add_zero] at hp ⊢; have := h2 hp; omega


theorem gap_ext (w : List ℕ) (i p q : ℕ) (hn : 0 < (occurrences w i).length)
    (hNq : w.length * q ≤ (occurrences w i).length * p)
    (H : ∀ j k, j < k → k < 2 * (occurrences w i).length →
      (((TT w i k : ℕ) : ℤ) - (TT w i j : ℕ) - 1) * (q : ℤ) < ((k : ℤ) - j) * (p : ℤ)) :
    ∀ k j, j < k →
      (((TT w i k : ℕ) : ℤ) - (TT w i j : ℕ) - 1) * (q : ℤ) < ((k : ℤ) - j) * (p : ℤ) := by
  set n := (occurrences w i).length with hn'
  have hNq' : ((w.length : ℕ) : ℤ) * q ≤ (n : ℤ) * p := by exact_mod_cast hNq
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro j hjk
    by_cases hj : n ≤ j
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + n := ⟨j - n, by omega⟩
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + n := ⟨k - n, by omega⟩
      have := ih k' (by omega) j' (by omega)
      rw [TT_add w i hn, TT_add w i hn]
      push_cast
      linarith
    · by_cases hk : k < 2 * n
      · exact H j k hjk hk
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + n := ⟨k - n, by omega⟩
        have := ih k' (by omega) j (by omega)
        rw [TT_add w i hn]
        push_cast
        nlinarith

theorem serves_of_gap (w : List ℕ) (i p q : ℕ) (hq : 0 < q) (hg : gapTest w i p q = true)
    (t W : ℕ) : ⌊(W : ℚ) / ((p : ℚ) / q)⌋₊ ≤ cnt (sch w) i t W := by
  unfold gapTest at hg
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hg
  obtain ⟨⟨hn1, hNq⟩, H⟩ := hg
  have hn : 0 < (occurrences w i).length := hn1
  have hN : 0 < w.length := by
    have := occ_lt w i 0 hn
    omega
  have hp : 0 < p := by
    by_contra hp
    have : p = 0 := by omega
    subst this
    have : 0 < w.length * q := Nat.mul_pos hN hq
    omega
  have H' : ∀ j k, j < k → k < 2 * (occurrences w i).length →
      (((TT w i k : ℕ) : ℤ) - (TT w i j : ℕ) - 1) * (q : ℤ) < ((k : ℤ) - j) * (p : ℤ) := by
    intro j k hjk hk
    have := H k hk j hjk
    rw [TT_ext w i k hk hn, TT_ext w i j (by omega) hn]
    exact this
  have G := gap_ext w i p q hn hNq H'
  -- shift
  have hshift : cnt (sch w) i t W = cnt (sch w) i (t + w.length) W := by
    unfold cnt
    congr 1
    apply List.filter_congr
    intro k _
    have : t + w.length + k = (t + k) + w.length := by ring
    have e : sch w (t + w.length + k) = sch w (t + k) := by
      unfold sch
      rw [this, Nat.add_mod_right]
    simp only [e]
  rw [hshift]
  set u := t + w.length with hu
  have hadd := cnt_add (sch w) i 0 u W
  simp only [zero_add] at hadd
  obtain ⟨hF1, hF2⟩ := F_spec w i hN hn u
  obtain ⟨hK1, hK2⟩ := F_spec w i hN hn (u + W)
  have hFpos : 0 < cnt (sch w) i 0 u := by
    by_contra hz
    have h0 : cnt (sch w) i 0 u = 0 := by omega
    rw [h0] at hF1
    have := occ_lt w i 0 hn
    simp only [TT, Nat.zero_mod, Nat.zero_div, zero_mul, add_zero] at hF1
    omega
  have hj := hF2 hFpos
  set Fu := cnt (sch w) i 0 u
  set Fk := cnt (sch w) i 0 (u + W)
  set c := cnt (sch w) i u W
  have hGG := G Fk (Fu - 1) (by omega)
  have e1 : ((Fk : ℤ) - ((Fu - 1 : ℕ) : ℤ)) = (c : ℤ) + 1 := by
    have : Fu - 1 + 1 = Fu := by omega
    omega
  rw [e1] at hGG
  have h3 : (W : ℤ) ≤ ((TT w i Fk : ℕ) : ℤ) - (TT w i (Fu - 1) : ℕ) - 1 := by omega
  have h4 : (W : ℤ) * q < ((c : ℤ) + 1) * p := by
    have : (W : ℤ) * q ≤ (((TT w i Fk : ℕ) : ℤ) - (TT w i (Fu - 1) : ℕ) - 1) * q :=
      mul_le_mul_of_nonneg_right h3 (by exact_mod_cast hq.le)
    linarith
  have h5 : W * q < (c + 1) * p := by exact_mod_cast h4
  have h6 : (W : ℚ) / ((p : ℚ) / q) < (c : ℚ) + 1 := by
    have hpq : (0 : ℚ) < p := by exact_mod_cast hp
    have hqq : (0 : ℚ) < q := by exact_mod_cast hq
    rw [div_div_eq_mul_div, div_lt_iff₀ hpq]
    exact_mod_cast h5
  have h7 : ⌊(W : ℚ) / ((p : ℚ) / q)⌋₊ < c + 1 := by
    rw [Nat.floor_lt (by positivity)]
    exact_mod_cast h6
  omega

end PinwheelDensity.ExactRange.Dev.LC3
end

section
set_option autoImplicit false

namespace PinwheelDensity.ExactRange.Dev.LC3

open PinwheelDensity.ExactRange PinwheelDensity.ExactRange.Dev.FoldAux

abbrev F2 (l m : List ℚ) : Prop := List.Forall₂ (· ≤ ·) l m

/-! ### Lemma C.1 -/

theorem wordServes_sched {w : List ℕ} {r : List ℚ} (h : wordServes w r = true) :
    RatSchedulable r := by
  unfold wordServes at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨-, h⟩ := h
  have key : ∀ i (hi : i < r.length), 0 < r[i] ∧ gapTest w i r[i].num.toNat r[i].den = true := by
    intro i hi
    have := h i hi
    simp only [List.getElem?_eq_getElem hi, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this
  refine ⟨?_, sch w, fun i hi => ?_⟩
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ha
    exact (key i hi).1
  · obtain ⟨hpos, hg⟩ := key i hi
    intro t W
    have hnum : ((r[i].num.toNat : ℕ) : ℚ) = (r[i].num : ℚ) := by
      have : 0 ≤ r[i].num := Rat.num_nonneg.2 hpos.le
      exact_mod_cast Int.toNat_of_nonneg this
    have := serves_of_gap w i r[i].num.toNat r[i].den r[i].den_pos hg t W
    rw [hnum, Rat.num_div_den] at this
    exact this

/-! ### Order lemmas -/

theorem F2_idx {l m : List ℚ} (h : F2 l m) {i : ℕ} {a d : ℚ} (ha : l[i]? = some a)
    (hd : m[i]? = some d) : a ≤ d := by
  obtain ⟨a', h1, h2⟩ := fle_getElem? h ha
  rw [h1] at hd
  cases hd
  exact h2

theorem F2_set_up {b u : List ℚ} (h : F2 b u) {i : ℕ} {d x : ℚ} (hd : b[i]? = some d)
    (hx : d ≤ x) : F2 b (u.set i x) := by
  induction h generalizing i with
  | nil => simp
  | @cons a c l m hac _ ih =>
    cases i with
    | zero =>
      simp at hd; subst hd
      simpa using List.Forall₂.cons hx ‹F2 l m›
    | succ i =>
      simp at hd
      simpa using List.Forall₂.cons hac (ih hd)

theorem F2_set_lo {l b : List ℚ} (h : F2 l b) {i : ℕ} {d x : ℚ} (hd : b[i]? = some d)
    (hx : x ≤ d) : F2 (l.set i x) b := by
  induction h generalizing i with
  | nil => simp
  | @cons a c l m hac _ ih =>
    cases i with
    | zero =>
      simp at hd; subst hd
      simpa using List.Forall₂.cons hx ‹F2 l m›
    | succ i =>
      simp at hd
      simpa using List.Forall₂.cons hac (ih hd)

theorem F2_map_max {l b : List ℚ} (h : F2 l b) {x y : ℚ} (hxy : x ≤ y)
    (hy : ∀ z ∈ b, y ≤ z) : F2 (l.map (max x)) b := by
  induction h with
  | nil => simp
  | @cons a c l m hac _ ih =>
    simp only [List.map_cons]
    refine List.Forall₂.cons (max_le (hxy.trans (hy c (by simp))) hac) (ih ?_)
    intro z hz; exact hy z (by simp [hz])

theorem prefixMax_le : ∀ (n : ℕ) (l b : List ℚ), l.length ≤ n → b.Pairwise (· ≤ ·) →
    F2 l b → F2 (prefixMax l) b := by
  intro n
  induction n with
  | zero =>
    intro l b hl _ h
    have : l = [] := List.length_eq_zero_iff.1 (by omega)
    subst this
    simpa [prefixMax] using h
  | succ n ih =>
    intro l b hl hb h
    cases h with
    | nil => simp [prefixMax]
    | @cons x y l' b' hxy h' =>
      rw [prefixMax]
      have hb' := List.pairwise_cons.1 hb
      refine List.Forall₂.cons hxy (ih _ _ (by simp at hl ⊢; omega) hb'.2 ?_)
      exact F2_map_max h' hxy hb'.1

theorem suffixMin_ge : ∀ (u b : List ℚ), b.Pairwise (· ≤ ·) → F2 b u → F2 b (suffixMin u) := by
  intro u
  induction u with
  | nil => intro b _ h; simpa [suffixMin] using h
  | cons x l ih =>
    intro b hb h
    cases h with
    | @cons y z b' _ hyx h' =>
      have hb' := List.pairwise_cons.1 hb
      have ih' := ih b' hb'.2 h'
      rw [suffixMin]
      cases hs : suffixMin l with
      | nil =>
        rw [hs] at ih'
        cases ih'
        exact List.Forall₂.cons hyx List.Forall₂.nil
      | cons y1 t =>
        rw [hs] at ih'
        cases ih' with
        | @cons z1 _ b'' _ hz1 h2 =>
          have : y ≤ z1 := hb'.1 z1 (by simp)
          exact List.Forall₂.cons (le_min hyx (this.trans hz1)) (List.Forall₂.cons hz1 h2)

theorem norm_box (sm : Bool) {ℓ u b : List ℚ} (hb : b.Pairwise (· ≤ ·)) (h1 : F2 ℓ b)
    (h2 : F2 b u) : F2 (nodeLo sm ℓ) b ∧ F2 b (nodeUp sm u) := by
  cases sm
  · exact ⟨h1, h2⟩
  · exact ⟨prefixMax_le _ ℓ b le_rfl hb h1, suffixMin_ge u b hb h2⟩

theorem acc_false (sm : Bool) {ℓ u b : List ℚ} (h1 : F2 (nodeLo sm ℓ) b) (h2 : F2 b (nodeUp sm u)) :
    acceptedOutright sm ℓ u = false := by
  unfold acceptedOutright
  cases sm
  · simp
  · simp only [Bool.true_and]
    simp only [nodeLo, nodeUp, if_true] at h1 h2 ⊢
    generalize prefixMax ℓ = lo at h1 ⊢
    generalize suffixMin u = up at h2 ⊢
    revert up
    induction h1 with
    | nil => intro up _; simp
    | @cons a c l m hac _ ih =>
      intro up h2
      cases h2 with
      | @cons _ e _ up' hce h2' =>
        simp only [List.zipWith_cons_cons, List.any_cons]
        have : ¬ (e < a) := not_lt.2 (hac.trans hce)
        simp [this, ih _ h2']

theorem densityQ_mono {b u : List ℚ} (h : F2 b u) (hp : ∀ x ∈ b, 0 < x) :
    densityQ u ≤ densityQ b := by
  induction h with
  | nil => simp [densityQ]
  | @cons a c l m hac _ ih =>
    have ha : 0 < a := hp a (by simp)
    have := ih (fun x hx => hp x (by simp [hx]))
    simp only [densityQ, List.map_cons, List.sum_cons] at this ⊢
    have h1 : 1 / c ≤ 1 / a := one_div_le_one_div_of_le ha hac
    linarith

theorem densityQ_idx {b u : List ℚ} (h : F2 b u) (hp : ∀ x ∈ b, 0 < x) {i : ℕ} {a c : ℚ}
    (ha : b[i]? = some a) (hc : u[i]? = some c) :
    1 / a - 1 / c ≤ densityQ b - densityQ u := by
  induction h generalizing i with
  | nil => simp at ha
  | @cons a' c' l m hac h' ih =>
    have hpos : 0 < a' := hp a' (by simp)
    have hp' : ∀ x ∈ l, 0 < x := fun x hx => hp x (by simp [hx])
    cases i with
    | zero =>
      simp at ha hc; subst ha; subst hc
      have := densityQ_mono h' hp'
      simp only [densityQ, List.map_cons, List.sum_cons] at this ⊢
      linarith
    | succ i =>
      simp at ha hc
      have := ih hp' ha hc
      have h1 : 1 / c' ≤ 1 / a' := one_div_le_one_div_of_le hpos hac
      simp only [densityQ, List.map_cons, List.sum_cons] at this ⊢
      linarith

theorem F2_zipWith {lo up b : List ℚ} (f : ℚ → ℚ → ℚ) (h1 : F2 lo b) (h2 : F2 b up)
    (hf : ∀ (i : ℕ) (a c d : ℚ), lo[i]? = some a → up[i]? = some c → b[i]? = some d → f a c ≤ d) :
    F2 (List.zipWith f lo up) b := by
  induction h1 generalizing up with
  | nil => simp
  | @cons a d l b' had h' ih =>
    cases h2 with
    | @cons _ c _ up' hdc h2' =>
      simp only [List.zipWith_cons_cons]
      refine List.Forall₂.cons (hf 0 a c d (by simp) (by simp) (by simp)) (ih h2' ?_)
      intro (i : ℕ) a1 c1 d1 ha hc hd
      exact hf (i + 1) a1 c1 d1 (by simpa using ha) (by simpa using hc) (by simpa using hd)

theorem tighten_le {β : ℚ} {lo up b : List ℚ} (h1 : F2 lo b) (h2 : F2 b up)
    (hp : ∀ x ∈ b, 0 < x) (hd : densityQ b < β) : F2 (tighten β lo up) b := by
  have hup := densityQ_mono h2 hp
  have hε : 0 < β - densityQ up := by linarith
  unfold tighten sumRecip
  refine F2_zipWith _ h1 h2 ?_
  intro i a c d ha hc hdd
  have had := F2_idx h1 ha hdd
  have hdc := F2_idx h2 hdd hc
  have hdpos : 0 < d := hp d (List.mem_of_getElem? hdd)
  have hcpos : 0 < c := lt_of_lt_of_le hdpos hdc
  have key := densityQ_idx h2 hp hdd hc
  have h3 : 1 / d - 1 / c < β - densityQ up := by linarith
  refine max_le had ?_
  set ε := β - densityQ up
  rw [div_le_iff₀ (by positivity)]
  rw [div_sub_div _ _ hdpos.ne' hcpos.ne', div_lt_iff₀ (by positivity)] at h3
  nlinarith

/-! ### Soundness of the tree -/

theorem tree_sound (sm : Bool) (β : ℚ) :
    ∀ (T : SplitTree) (ℓ u : List ℚ), checkTree sm β T ℓ u = true →
      ∀ b : List ℚ, b.Pairwise (· ≤ ·) → IsBoxMember ℓ u β b → RatSchedulable b := by
  intro T
  induction T with
  | empty =>
    intro ℓ u hT b hb hmem
    obtain ⟨hm1, hm2, hpos, hd⟩ := hmem
    have h1 := (leAll_iff _ _).1 hm1
    have h2 := (leAll_iff _ _).1 hm2
    obtain ⟨n1, n2⟩ := norm_box sm hb h1 h2
    have hacc := acc_false sm n1 n2
    simp only [checkTree, hacc, Bool.false_or, decide_eq_true_eq] at hT
    have := densityQ_mono n2 hpos
    unfold sumRecip at hT
    linarith
  | cert r π w =>
    intro ℓ u hT b hb hmem
    obtain ⟨hm1, hm2, hpos, hd⟩ := hmem
    have h1 := (leAll_iff _ _).1 hm1
    have h2 := (leAll_iff _ _).1 hm2
    obtain ⟨n1, n2⟩ := norm_box sm hb h1 h2
    have hacc := acc_false sm n1 n2
    simp only [checkTree, hacc, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq] at hT
    obtain ⟨hw, hT⟩ := hT
    rcases hT with hT | hT
    · have := densityQ_mono n2 hpos
      unfold sumRecip at hT
      linarith
    · have hr := wordServes_sched hw
      have hL := tighten_le n1 n2 hpos hd
      cases hap : applyPairs π (sortQ (tighten β (nodeLo sm ℓ) (nodeUp sm u))) with
      | none => rw [hap] at hT; simp at hT
      | some v =>
        rw [hap] at hT
        exact dominated_sound hL hap hr hT
  | split i x T₁ T₂ ih1 ih2 =>
    intro ℓ u hT b hb hmem
    obtain ⟨hm1, hm2, hpos, hd⟩ := hmem
    have h1 := (leAll_iff _ _).1 hm1
    have h2 := (leAll_iff _ _).1 hm2
    obtain ⟨n1, n2⟩ := norm_box sm hb h1 h2
    have hacc := acc_false sm n1 n2
    simp only [checkTree, hacc, Bool.false_or] at hT
    cases hlo : (nodeLo sm ℓ)[i]? with
    | none => rw [hlo] at hT; simp at hT
    | some a =>
      cases hup : (nodeUp sm u)[i]? with
      | none => rw [hlo, hup] at hT; simp at hT
      | some c =>
        rw [hlo, hup] at hT
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hT
        obtain ⟨⟨⟨-, -⟩, hT1⟩, hT2⟩ := hT
        obtain ⟨d, hbd, -⟩ := fle_getElem? n1 hlo
        rcases le_total d x with hdx | hdx
        · exact ih1 _ _ hT1 b hb
            ⟨(leAll_iff _ _).2 n1, (leAll_iff _ _).2 (F2_set_up n2 hbd hdx), hpos, hd⟩
        · exact ih2 _ _ hT2 b hb
            ⟨(leAll_iff _ _).2 (F2_set_lo n1 hbd hdx), (leAll_iff _ _).2 n2, hpos, hd⟩

end PinwheelDensity.ExactRange.Dev.LC3

namespace PinwheelDensity.ExactRange

theorem chk_prop_C_3 (sortedMode : Bool) (β : ℚ) (T : SplitTree) (ℓ u : List ℚ)
    (hT : checkTree sortedMode β T ℓ u = true) (b : List ℚ) (hb : b.Pairwise (· ≤ ·))
    (hmem : IsBoxMember ℓ u β b) : RatSchedulable b :=
  Dev.LC3.tree_sound sortedMode β T ℓ u hT b hb hmem

end PinwheelDensity.ExactRange
end

theorem solution : type_of% @PinwheelDensity.ExactRange.chk_prop_C_3 := @PinwheelDensity.ExactRange.chk_prop_C_3
