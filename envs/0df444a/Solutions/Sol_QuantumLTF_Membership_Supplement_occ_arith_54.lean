-- Prove2me | solution 1 for QuantumLTF.Membership.Supplement.occ_arith_54
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-25T02:41:14.682808+00:00
-- url     : https://prove2.me/submissions/1870ae03-0774-4d10-be3e-d856f9f8ac00

import Mathlib
import Definitions.Def_QuantumLTF_Membership_Supplement_occArith54

set_option autoImplicit false

namespace QuantumLTF.Membership.Supplement

open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router

namespace OccArithImpl

lemma prefSum_eq_excl_add {m : ℕ} (α : Fin m → ℕ) (i : Fin m) :
    prefSum54 α i = exclPrefSum54 α i + α i := by
  dsimp only [prefSum54, exclPrefSum54]
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase Finset.univ (fun j : Fin m => if j < i then α j else 0) (Finset.mem_univ i)]
  simp only [le_refl, ↓reduceIte, lt_irrefl, zero_add]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hne : j ≠ i := (Finset.mem_erase.mp hj).1
  have hiff : j ≤ i ↔ j < i :=
    ⟨fun h => lt_of_le_of_ne h hne, fun h => le_of_lt h⟩
  simp [hiff]

lemma prefSum_mono {m : ℕ} (α : Fin m → ℕ) : Monotone (prefSum54 α) := by
  intro i j hij
  refine Finset.sum_le_sum fun r _ => ?_
  split_ifs with h1 h2
  · exact le_rfl
  · exact False.elim (h2 (le_trans h1 hij))
  · exact Nat.zero_le _
  · exact le_rfl

lemma exclPrefSum_le_prefSum_of_lt {m : ℕ} (α : Fin m → ℕ) {i j : Fin m} (hij : i < j) :
    prefSum54 α i ≤ exclPrefSum54 α j := by
  dsimp only [prefSum54, exclPrefSum54]
  refine Finset.sum_le_sum fun r _ => ?_
  split_ifs with h1 h2
  · exact le_rfl
  · exact False.elim (h2 (lt_of_le_of_lt h1 hij))
  · exact Nat.zero_le _
  · exact le_rfl

lemma exclPrefSum_zero {m : ℕ} (α : Fin (m + 1) → ℕ) :
    exclPrefSum54 α 0 = 0 := by
  simp [exclPrefSum54]

lemma prefSum_last {m : ℕ} (α : Fin (m + 1) → ℕ) :
    prefSum54 α (Fin.last m) = ∑ j : Fin (m + 1), α j := by
  dsimp only [prefSum54]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Fin.le_last]

lemma prefSum_le_sum {m : ℕ} (α : Fin m → ℕ) (i : Fin m) :
    prefSum54 α i ≤ ∑ j : Fin m, α j := by
  refine Finset.sum_le_sum fun j _ => ?_
  split_ifs <;> omega

lemma modeOf_lt {m : ℕ} (α : Fin m → ℕ) {N c : ℕ} (hN : ∑ j : Fin m, α j = N) (hc : c < N) :
    modeOf54 α c < m := by
  have hm : 0 < m := by
    by_contra h0
    have hm0 : m = 0 := by omega
    subst hm0
    simp at hN
    omega
  have hlast : ¬ prefSum54 α ⟨m - 1, by omega⟩ ≤ c := by
    have hEq : prefSum54 α ⟨m - 1, by omega⟩ = ∑ j : Fin m, α j := by
      dsimp only [prefSum54]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hj_le : j.1 ≤ m - 1 := Nat.le_pred_of_lt j.isLt
      have hj : j ≤ ⟨m - 1, by omega⟩ := Fin.le_iff_val_le_val.mpr hj_le
      simp [hj]
    rw [hEq, hN]
    omega
  have hsub : (Finset.univ.filter fun r : Fin m => prefSum54 α r ≤ c) ⊂ Finset.univ := by
    rw [Finset.ssubset_univ_iff]
    intro hAll
    have hmem : (⟨m - 1, by omega⟩ : Fin m) ∈
        Finset.univ.filter fun r : Fin m => prefSum54 α r ≤ c := by
      rw [hAll]; exact Finset.mem_univ _
    exact hlast (Finset.mem_filter.mp hmem).2
  have hcard := Finset.card_lt_card hsub
  simpa [modeOf54] using hcard

lemma modeOf_spec {m : ℕ} (α : Fin m → ℕ) {N c : ℕ} (hN : ∑ j : Fin m, α j = N) (hc : c < N) :
    let i : Fin m := ⟨modeOf54 α c, modeOf_lt α hN hc⟩
    exclPrefSum54 α i ≤ c ∧ c < prefSum54 α i := by
  intro i
  let S : Finset (Fin m) := Finset.univ.filter fun r : Fin m => prefSum54 α r ≤ c
  have hS_down : ∀ r s : Fin m, r ≤ s → s ∈ S → r ∈ S := by
    intro r s hrs hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      le_trans (prefSum_mono α hrs) (Finset.mem_filter.mp hs).2⟩
  have hS_eq : S = Finset.univ.filter fun r : Fin m => r.1 < S.card := by
    ext r
    constructor
    · intro hr
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have hsub : (Finset.univ.filter fun s : Fin m => s ≤ r) ⊆ S := by
        intro s hs
        exact hS_down s r (Finset.mem_filter.mp hs).2 hr
      have hcard_le := Finset.card_le_card hsub
      have hcard_eq : (Finset.univ.filter fun s : Fin m => s ≤ r).card = r.1 + 1 := by
        have himg : (Finset.univ.filter fun s : Fin m => s ≤ r).image Fin.val =
            Finset.range (r.1 + 1) := by
          ext x
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_range]
          constructor
          · rintro ⟨s, hs, rfl⟩
            exact Nat.lt_succ_of_le (Fin.le_iff_val_le_val.mp hs)
          · intro hx
            exact ⟨⟨x, by omega⟩, Fin.le_iff_val_le_val.mpr (Nat.lt_succ_iff.mp hx), rfl⟩
        rw [← Finset.card_image_of_injective _ Fin.val_injective, himg, Finset.card_range]
      rw [hcard_eq] at hcard_le
      omega
    · intro hr
      have hr_lt : r.1 < S.card := (Finset.mem_filter.mp hr).2
      by_contra hnot
      have hsub : S ⊆ Finset.univ.filter fun s : Fin m => s.1 < r.1 := by
        intro s hs
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        by_contra hge
        have hle : r ≤ s := Fin.le_iff_val_le_val.mpr (Nat.le_of_not_lt hge)
        exact hnot (hS_down r s hle hs)
      have hcard_le := Finset.card_le_card hsub
      have hcard_lt : (Finset.univ.filter fun s : Fin m => s.1 < r.1).card ≤ r.1 := by
        have himg : (Finset.univ.filter fun s : Fin m => s.1 < r.1).image Fin.val ⊆
            Finset.range r.1 := by
          intro x hx
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx
          rcases hx with ⟨s, hs, rfl⟩
          exact Finset.mem_range.mpr hs
        rw [← Finset.card_image_of_injective _ Fin.val_injective]
        exact le_trans (Finset.card_le_card himg) (by simp)
      omega
  have hi_not : i ∉ S := by
    rw [hS_eq, Finset.mem_filter]
    simp [i, modeOf54, S]
  have hlt_pref : c < prefSum54 α i := by
    by_contra hle
    exact hi_not (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.le_of_not_lt hle⟩)
  have hexcl : exclPrefSum54 α i ≤ c := by
    rcases Nat.eq_zero_or_pos i.1 with hi0 | hipos
    · have hi_eq : i = ⟨0, i.pos⟩ := Fin.ext hi0
      rw [hi_eq]
      have h0 : exclPrefSum54 α ⟨0, i.pos⟩ = 0 := by
        dsimp only [exclPrefSum54]
        exact Finset.sum_eq_zero fun j _ => by
          rw [if_neg (by intro h; have := Fin.lt_def.mp h; dsimp at this; omega)]
      rw [h0]; exact Nat.zero_le _
    · let prev : Fin m := ⟨i.1 - 1, by omega⟩
      have hprev_in : prev ∈ S := by
        rw [hS_eq, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        change i.1 - 1 < S.card
        have : i.1 = S.card := rfl
        omega
      have hprev_le : prefSum54 α prev ≤ c := (Finset.mem_filter.mp hprev_in).2
      have heq : exclPrefSum54 α i = prefSum54 α prev := by
        dsimp only [exclPrefSum54, prefSum54]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hiff : j < i ↔ j ≤ prev := by
          rw [Fin.lt_def, Fin.le_iff_val_le_val]
          dsimp [prev]; omega
        simp [hiff]
      rw [heq]; exact hprev_le
  exact ⟨hexcl, hlt_pref⟩

lemma modeOf_eq_iff {m : ℕ} (α : Fin m → ℕ) {N c : ℕ} (hN : ∑ j : Fin m, α j = N) (hc : c < N)
    (r : Fin m) :
    modeOf54 α c = r.1 ↔ exclPrefSum54 α r ≤ c ∧ c < prefSum54 α r := by
  constructor
  · intro h
    have hr : r = ⟨modeOf54 α c, modeOf_lt α hN hc⟩ := Fin.ext h.symm
    rw [hr]
    exact modeOf_spec α hN hc
  · rintro ⟨h1, h2⟩
    have hsp := modeOf_spec α hN hc
    set i : Fin m := ⟨modeOf54 α c, modeOf_lt α hN hc⟩
    change i.1 = r.1
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := exclPrefSum_le_prefSum_of_lt α (Fin.lt_def.mpr hlt)
      omega
    · have := exclPrefSum_le_prefSum_of_lt α (Fin.lt_def.mpr hgt)
      omega

lemma modeOf_count {m : ℕ} (α : Fin m → ℕ) {N : ℕ} (hN : ∑ j : Fin m, α j = N) (r : Fin m) :
    (Finset.univ.filter fun c : Fin N => modeOf54 α c.1 = r.1).card = α r := by
  have himg : (Finset.univ.filter fun c : Fin N => modeOf54 α c.1 = r.1).image Fin.val =
      Finset.Ico (exclPrefSum54 α r) (prefSum54 α r) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ico]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact (modeOf_eq_iff α hN c.isLt r).mp hc
    · intro hx
      have hle := prefSum_le_sum α r
      have hxN : x < N := by omega
      exact ⟨⟨x, hxN⟩, (modeOf_eq_iff α hN hxN r).mpr hx, rfl⟩
  rw [← Finset.card_image_of_injective _ Fin.val_injective, himg, Nat.card_Ico,
      prefSum_eq_excl_add α r]
  omega

/-! ### `[LCG26, Section V]` Tuple List & Key Orderings -/

lemma lex2_lt_iff {α β : Type*} [LinearOrder α] [LinearOrder β]
    (a₁ : α) (b₁ : β) (a₂ : α) (b₂ : β) :
    (toLex (a₁, b₁) : α ×ₗ β) < toLex (a₂, b₂) ↔ a₁ < a₂ ∨ (a₁ = a₂ ∧ b₁ < b₂) := by
  simp [Prod.Lex.lt_iff]

lemma lex2_lt_fst {α β : Type*} [LinearOrder α] [LinearOrder β]
    {a₁ a₂ : α} (b₁ b₂ : β) (h : a₁ < a₂) :
    (toLex (a₁, b₁) : α ×ₗ β) < toLex (a₂, b₂) :=
  (lex2_lt_iff _ _ _ _).mpr (Or.inl h)

lemma lex2_lt_snd {α β : Type*} [LinearOrder α] [LinearOrder β]
    (a : α) {b₁ b₂ : β} (h : b₁ < b₂) :
    (toLex (a, b₁) : α ×ₗ β) < toLex (a, b₂) :=
  (lex2_lt_iff _ _ _ _).mpr (Or.inr ⟨rfl, h⟩)

lemma pairwise_finRange_lt (k : ℕ) : (List.finRange k).Pairwise (· < ·) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  simpa using hij

lemma length_filter_finRange_lt' (k t : ℕ) (ht : t ≤ k) :
    ((List.finRange k).filter (fun j => decide (j.1 < t))).length = t := by
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange k).filter _)]
  have himg : ((List.finRange k).filter (fun j => decide (j.1 < t))).toFinset.image Fin.val =
      Finset.range t := by
    ext x
    simp only [Finset.mem_image, List.mem_toFinset, List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq, Finset.mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact hj
    · intro hx; exact ⟨⟨x, by omega⟩, hx, rfl⟩
  rw [← Finset.card_image_of_injective _ Fin.val_injective, himg, Finset.card_range]

/-- Helper: strict pairwise inequality from `Pairwise (≤)` + `Nodup` keys. -/
lemma pairwise_lt_of_pairwise_le_of_nodup {α κ : Type*} [LinearOrder κ]
    (key : α → κ) (L : List α)
    (hnd : (L.map key).Nodup)
    (hle : L.Pairwise (fun x y => key x ≤ key y)) :
    L.Pairwise (fun x y => key x < key y) := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    rw [List.pairwise_cons] at hle ⊢
    rw [List.map_cons, List.nodup_cons] at hnd
    refine ⟨fun y hy => ?_, ih hnd.2 hle.2⟩
    have hxy := hle.1 y hy
    have hne : key x ≠ key y := fun h => hnd.1 (h ▸ List.mem_map_of_mem hy)
    exact lt_of_le_of_ne hxy hne

/-- Helper: `mergeSort` on `(key · ≤ key ·)` yields `Pairwise (fun x y => key x ≤ key y)`. -/
lemma pairwise_le_mergeSort {α κ : Type*} [LinearOrder κ]
    (key : α → κ) (L : List α) :
    (L.mergeSort (fun x y => decide (key x ≤ key y))).Pairwise (fun x y => key x ≤ key y) := by
  have hp := List.pairwise_mergeSort (le := fun x y => decide (key x ≤ key y))
    (fun a b c => by
      intro h1 h2
      rw [decide_eq_true_iff] at h1 h2 ⊢
      exact le_trans h1 h2)
    (fun a b => by
      rcases le_total (key a) (key b) with h | h <;> simp [h]) L
  exact hp.imp fun h => decide_eq_true_eq.mp h

/-- Helper: two `List.Perm` lists sorted by an injective key `key` on elements are equal. -/
lemma perm_eq_of_sorted_of_inj {α κ : Type*} [LinearOrder κ]
    (key : α → κ) (L₁ L₂ : List α)
    (hperm : List.Perm L₁ L₂)
    (h1 : L₁.Pairwise (fun x y => key x ≤ key y))
    (h2 : L₂.Pairwise (fun x y => key x ≤ key y))
    (hinj : ∀ x ∈ L₂, ∀ y ∈ L₂, key x = key y → x = y) :
    L₁ = L₂ := by
  induction L₁ generalizing L₂ with
  | nil =>
    exact (List.perm_nil.mp hperm.symm).symm
  | cons x xs ih =>
    cases L₂ with
    | nil =>
      exact absurd (List.perm_nil.mp hperm) (List.cons_ne_nil x xs)
    | cons y ys =>
      rw [List.pairwise_cons] at h1 h2
      have hx_in : x ∈ y :: ys := hperm.mem_iff.mp List.mem_cons_self
      have hy_in : y ∈ x :: xs := hperm.mem_iff.mpr List.mem_cons_self
      have hkx : key y ≤ key x := by
        rcases List.mem_cons.mp hx_in with rfl | hx_ys
        · exact le_rfl
        · exact h2.1 x hx_ys
      have hky : key x ≤ key y := by
        rcases List.mem_cons.mp hy_in with rfl | hy_xs
        · exact le_rfl
        · exact h1.1 y hy_xs
      have hxy_k : key x = key y := le_antisymm hky hkx
      have hxy : x = y := hinj x hx_in y List.mem_cons_self hxy_k
      subst hxy
      congr 1
      apply ih ys (List.Perm.cons_inv hperm) h1.2 h2.2
      intro a ha b hb hab
      exact hinj a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem x hb) hab

lemma wtilde2_length {m : ℕ} (α : Fin m → ℕ) (N : ℕ) :
    (wtilde2_54 α N).length = m + N := by
  simp [wtilde2_54]

lemma wtilde2_keyW2_strict {m : ℕ} (α : Fin m → ℕ) (N : ℕ) :
    ((wtilde2_54 α N).map keyW2_54).Pairwise (· < ·) := by
  dsimp only [wtilde2_54]
  rw [List.map_append, List.pairwise_append]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.map_map, List.pairwise_map]
    exact (pairwise_finRange_lt m).imp fun {i j} hij => by
      dsimp only [Function.comp_def, keyW2_54]
      exact lex2_lt_fst (prefSum54 α i) (prefSum54 α j) (Fin.lt_def.mp hij)
  · rw [List.map_map, List.pairwise_map]
    exact (pairwise_finRange_lt N).imp fun {i j} hij => by
      dsimp only [Function.comp_def, keyW2_54]
      exact lex2_lt_snd m (Fin.lt_def.mp hij)
  · intro x hx y hy
    simp only [List.mem_map, List.mem_finRange, true_and] at hx hy
    rcases hx with ⟨t1, ht1, rfl⟩
    rcases hy with ⟨t2, ht2, rfl⟩
    rcases ht1 with ⟨i, rfl⟩
    rcases ht2 with ⟨j, rfl⟩
    exact lex2_lt_fst (prefSum54 α i) j.1 i.isLt

/-- Key `keyW3_54` strictly separates all elements of `wtilde2_54`. -/
lemma wtilde2_keyW3_nodup {m : ℕ} (α : Fin m → ℕ) (N : ℕ) :
    ((wtilde2_54 α N).map keyW3_54).Nodup := by
  dsimp only [wtilde2_54]
  rw [List.map_append, List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.map_map]
    refine List.Nodup.map ?_ (List.nodup_finRange m)
    intro i j h
    exact Fin.ext (congrArg (fun p : ℕ ×ₗ ℕ => (ofLex p).2) h)
  · rw [List.map_map]
    refine List.Nodup.map ?_ (List.nodup_finRange N)
    intro i j h
    exact Fin.ext (congrArg (fun p : ℕ ×ₗ ℕ => (ofLex p).1) h)
  · intro x hx y hy heq
    simp only [List.mem_map, List.mem_finRange, true_and] at hx hy
    rcases hx with ⟨t1, ht1, rfl⟩
    rcases hy with ⟨t2, ht2, rfl⟩
    rcases ht1 with ⟨i, rfl⟩
    rcases ht2 with ⟨j, rfl⟩
    have ha := congrArg (fun p : ℕ ×ₗ ℕ => (ofLex p).2) heq
    dsimp [keyW3_54] at ha
    omega

lemma wtilde3Rank_mode {m : ℕ} (α : Fin m → ℕ) {N : ℕ} (hN : ∑ j : Fin m, α j = N)
    (i : Fin m) :
    wtilde3Rank54 α N (i.1, 0, prefSum54 α i) = prefSum54 α i + i.1 := by
  dsimp only [wtilde3Rank54, wtilde2_54]
  rw [List.filter_append, List.length_append]
  have hL : (((List.finRange m).map (fun r => (r.1, 0, prefSum54 α r))).filter
      (fun u => decide (keyW3_54 u < keyW3_54 (i.1, 0, prefSum54 α i)))).length = i.1 := by
    rw [List.filter_map, List.length_map]
    have heq : (List.finRange m).filter (fun r => decide (keyW3_54 (r.1, 0, prefSum54 α r) <
        keyW3_54 (i.1, 0, prefSum54 α i))) = (List.finRange m).filter (fun r => decide (r.1 < i.1)) := by
      congr 1; funext r
      apply decide_eq_decide.mpr
      dsimp only [keyW3_54]
      rw [lex2_lt_iff]
      constructor
      · rintro (h1 | ⟨_, h2⟩)
        · by_contra hge
          have hir : i ≤ r := Fin.le_iff_val_le_val.mpr (Nat.le_of_not_lt hge)
          have hmono := prefSum_mono α hir
          omega
        · exact h2
      · intro h
        have hri : r ≤ i := Fin.le_iff_val_le_val.mpr (le_of_lt h)
        have hle := prefSum_mono α hri
        rcases eq_or_lt_of_le hle with he | hlt
        · exact Or.inr ⟨he, h⟩
        · exact Or.inl hlt
    change ((List.finRange m).filter (fun r => decide (keyW3_54 (r.1, 0, prefSum54 α r) <
        keyW3_54 (i.1, 0, prefSum54 α i)))).length = i.1
    rw [heq, length_filter_finRange_lt' m i.1 (le_of_lt i.isLt)]
  have hR : (((List.finRange N).map (fun j => (m, 0, j.1))).filter
      (fun u => decide (keyW3_54 u < keyW3_54 (i.1, 0, prefSum54 α i)))).length = prefSum54 α i := by
    rw [List.filter_map, List.length_map]
    have heq : (List.finRange N).filter (fun j => decide (keyW3_54 (m, 0, j.1) <
        keyW3_54 (i.1, 0, prefSum54 α i))) =
        (List.finRange N).filter (fun j => decide (j.1 < prefSum54 α i)) := by
      congr 1; funext j
      apply decide_eq_decide.mpr
      dsimp only [keyW3_54]
      rw [lex2_lt_iff]
      constructor
      · rintro (h1 | ⟨_, h2⟩)
        · exact h1
        · exfalso; have := i.isLt; omega
      · intro h
        exact Or.inl h
    change ((List.finRange N).filter (fun j => decide (keyW3_54 (m, 0, j.1) <
        keyW3_54 (i.1, 0, prefSum54 α i)))).length = prefSum54 α i
    rw [heq, length_filter_finRange_lt' N (prefSum54 α i) (by rw [← hN]; exact prefSum_le_sum α i)]
  rw [hL, hR, add_comm]

lemma wtilde3Rank_empty {m : ℕ} (α : Fin m → ℕ) (N : ℕ) (j : Fin N) :
    wtilde3Rank54 α N (m, 0, j.1) = modeOf54 α j.1 + j.1 := by
  dsimp only [wtilde3Rank54, wtilde2_54]
  rw [List.filter_append, List.length_append]
  have hL : (((List.finRange m).map (fun r => (r.1, 0, prefSum54 α r))).filter
      (fun u => decide (keyW3_54 u < keyW3_54 (m, 0, j.1)))).length = modeOf54 α j.1 := by
    rw [List.filter_map, List.length_map]
    have heq : (List.finRange m).filter (fun r => decide (keyW3_54 (r.1, 0, prefSum54 α r) <
        keyW3_54 (m, 0, j.1))) =
        (List.finRange m).filter (fun r => decide (prefSum54 α r ≤ j.1)) := by
      congr 1; funext r
      apply decide_eq_decide.mpr
      dsimp only [keyW3_54]
      rw [lex2_lt_iff]
      constructor
      · rintro (h1 | ⟨he, _⟩)
        · exact le_of_lt h1
        · exact le_of_eq he
      · intro h
        rcases eq_or_lt_of_le h with he | hlt
        · exact Or.inr ⟨he, r.isLt⟩
        · exact Or.inl hlt
    change ((List.finRange m).filter (fun r => decide (keyW3_54 (r.1, 0, prefSum54 α r) <
        keyW3_54 (m, 0, j.1)))).length = modeOf54 α j.1
    rw [heq]
    have hcard : ((List.finRange m).filter (fun r => decide (prefSum54 α r ≤ j.1))).length =
        (Finset.univ.filter fun r : Fin m => prefSum54 α r ≤ j.1).card := by
      rw [← List.toFinset_card_of_nodup ((List.nodup_finRange m).filter _)]
      congr 1
      ext r
      simp [Finset.mem_filter]
    rw [hcard]
    rfl
  have hR : (((List.finRange N).map (fun k => (m, 0, k.1))).filter
      (fun u => decide (keyW3_54 u < keyW3_54 (m, 0, j.1)))).length = j.1 := by
    rw [List.filter_map, List.length_map]
    have heq : (List.finRange N).filter (fun k => decide (keyW3_54 (m, 0, k.1) <
        keyW3_54 (m, 0, j.1))) =
        (List.finRange N).filter (fun k => decide (k.1 < j.1)) := by
      congr 1; funext k
      apply decide_eq_decide.mpr
      dsimp only [keyW3_54]
      rw [lex2_lt_iff]
      constructor
      · rintro (h1 | ⟨_, h2⟩)
        · exact h1
        · exact absurd h2 (lt_irrefl m)
      · intro h
        exact Or.inl h
    change ((List.finRange N).filter (fun k => decide (keyW3_54 (m, 0, k.1) <
        keyW3_54 (m, 0, j.1)))).length = j.1
    rw [heq, length_filter_finRange_lt' N j.1 (le_of_lt j.isLt)]
  rw [hL, hR]

lemma wtilde3_length {m : ℕ} (α : Fin m → ℕ) (N : ℕ) :
    (wtilde3_54 α N).length = m + N := by
  simp [wtilde3_54, wtilde2_length]

/-- Generic lemma: in a `mergeSort`-sorted list of elements whose keys `key` are `Nodup`,
the position of any element `t ∈ L` equals `(L.filter (key · < key t)).length`. -/
lemma index_in_sorted_of_nodup {α : Type*} {κ : Type*} [LinearOrder κ]
    (key : α → κ) (L : List α) (hnd : (L.map key).Nodup)
    (t : α) (_ht : t ∈ L) (pos : ℕ)
    (hpos : pos < (L.mergeSort (fun x y => decide (key x ≤ key y))).length)
    (heq : (L.mergeSort (fun x y => decide (key x ≤ key y)))[pos] = t) :
    pos = (L.filter (fun u => decide (key u < key t))).length := by
  set S := L.mergeSort (fun x y => decide (key x ≤ key y))
  have hperm : List.Perm S L := List.mergeSort_perm L _
  have hS_nd : (S.map key).Nodup := hperm.map key |>.nodup_iff.mpr hnd
  have hsorted : S.Pairwise (fun x y => key x ≤ key y) := pairwise_le_mergeSort key L
  have hlt : S.Pairwise (fun x y => key x < key y) :=
    pairwise_lt_of_pairwise_le_of_nodup key S hS_nd hsorted
  have hfilter_perm : List.Perm (S.filter (fun u => decide (key u < key t)))
      (L.filter (fun u => decide (key u < key t))) := hperm.filter _
  rw [← hfilter_perm.length_eq]
  have htake : S.filter (fun u => decide (key u < key t)) = S.take pos := by
    have hdrop_eq : S.drop pos = t :: S.drop (pos + 1) := by
      rw [← heq]
      exact List.drop_eq_getElem_cons hpos
    have hsplit : S = S.take pos ++ t :: S.drop (pos + 1) := by
      rw [← hdrop_eq, List.take_append_drop]
    conv_lhs => rw [hsplit]
    rw [List.filter_append, List.filter_cons]
    have hleft : (S.take pos).filter (fun u => decide (key u < key t)) = S.take pos := by
      rw [List.filter_eq_self]
      intro u hu
      simp only [decide_eq_true_eq]
      rcases List.getElem_of_mem hu with ⟨j, hj, rfl⟩
      have hj_len : j < pos := by
        have := List.length_take_le pos S
        omega
      have hj_S : j < S.length := by omega
      have hget : (S.take pos)[j] = S[j] := List.getElem_take
      rw [hget, ← heq]
      exact (List.pairwise_iff_getElem.mp hlt) j pos hj_S hpos hj_len
    have ht_not : decide (key t < key t) = false := decide_eq_false (lt_irrefl _)
    have hright : (S.drop (pos + 1)).filter (fun u => decide (key u < key t)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro u hu
      rcases List.getElem_of_mem hu with ⟨j, hj, rfl⟩
      have hlen_drop : (S.drop (pos + 1)).length = S.length - (pos + 1) := List.length_drop
      have hj_S : pos + 1 + j < S.length := by omega
      have hget : (S.drop (pos + 1))[j] = S[pos + 1 + j] := List.getElem_drop
      rw [hget]
      have hgt : key t < key S[pos + 1 + j] := by
        rw [← heq]
        exact (List.pairwise_iff_getElem.mp hlt) pos (pos + 1 + j) hpos hj_S (by omega)
      simp only [decide_eq_true_eq]
      exact not_lt_of_gt hgt
    rw [hleft, ht_not, hright]
    simp
  rw [htake, List.length_take_of_le (le_of_lt hpos)]

/-- At any position `pos` of `wtilde3_54`, if `a = m` then `b := pos - c = modeOf54 α c`,
and if `a < m` then `c = prefSum54 α ⟨a, _⟩ = pos - a`. -/
theorem wtilde3_pos_spec {m : ℕ} (α : Fin m → ℕ) {N : ℕ} (hN : ∑ j : Fin m, α j = N)
    (pos : ℕ) (hpos : pos < (wtilde3_54 α N).length) :
    let t := (wtilde3_54 α N)[pos]
    (t.1 = m → t.2.2 < N ∧ pos ≥ t.2.2 ∧ pos - t.2.2 = modeOf54 α t.2.2) ∧
    (t.1 < m → ∃ hi : t.1 < m, t.2.2 = prefSum54 α ⟨t.1, hi⟩ ∧ pos ≥ t.1 ∧ pos - t.1 = t.2.2) := by
  intro t
  have hpos' : pos < ((wtilde2_54 α N).mergeSort (fun x y => decide (keyW3_54 x ≤ keyW3_54 y))).length := hpos
  have ht_mem : t ∈ wtilde2_54 α N := (List.mergeSort_perm _ _).mem_iff.mp (List.getElem_mem hpos')
  have hrank : pos = wtilde3Rank54 α N t :=
    index_in_sorted_of_nodup keyW3_54 (wtilde2_54 α N) (wtilde2_keyW3_nodup α N) t ht_mem pos hpos' rfl
  have ht_mem' := ht_mem
  simp only [wtilde2_54, List.mem_append, List.mem_map, List.mem_finRange, true_and] at ht_mem'
  rcases ht_mem' with ⟨i, hi⟩ | ⟨j, hj⟩
  · have ha : t.1 = i.1 := by rw [← hi]
    have hc : t.2.2 = prefSum54 α i := by rw [← hi]
    have hlt : t.1 < m := ha ▸ i.isLt
    refine ⟨fun hm => absurd hm (ne_of_lt hlt), fun _ => ?_⟩
    have hi_eq : (⟨t.1, hlt⟩ : Fin m) = i := Fin.ext ha
    rw [← hi, wtilde3Rank_mode α hN i] at hrank
    refine ⟨hlt, by rw [hi_eq, hc], ?_, ?_⟩ <;> omega
  · have ha : t.1 = m := by rw [← hj]
    have hc : t.2.2 = j.1 := by rw [← hj]
    refine ⟨fun _ => ?_, fun hlt => absurd ha (ne_of_lt hlt)⟩
    rw [← hj, wtilde3Rank_empty α N j] at hrank
    rw [hc]
    refine ⟨j.isLt, ?_, ?_⟩ <;> omega

lemma wtilde6_keyW3_nodup {m : ℕ} (α : Fin m → ℕ) (N : ℕ) :
    ((wtilde6_54 α N).map keyW3_54).Nodup := by
  dsimp only [wtilde6_54]
  rw [List.map_append, List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.map_map]
    refine List.Nodup.map ?_ (List.nodup_finRange m)
    intro i j h
    exact Fin.ext (congrArg (fun p : ℕ ×ₗ ℕ => (ofLex p).2) h)
  · rw [List.map_map]
    refine List.Nodup.map ?_ (List.nodup_finRange N)
    intro i j h
    exact Fin.ext (congrArg (fun p : ℕ ×ₗ ℕ => (ofLex p).1) h)
  · intro x hx y hy heq
    simp only [List.mem_map, List.mem_finRange, true_and] at hx hy
    rcases hx with ⟨t1, ht1, rfl⟩
    rcases hy with ⟨t2, ht2, rfl⟩
    rcases ht1 with ⟨i, rfl⟩
    rcases ht2 with ⟨j, rfl⟩
    have ha := congrArg (fun p : ℕ ×ₗ ℕ => (ofLex p).2) heq
    dsimp [keyW3_54] at ha
    omega

lemma keyW8_order_aux {m N : ℕ} (α : Fin m → ℕ) (hN : ∑ j : Fin m, α j = N)
    (t1 t2 : Sec5Rec54) (ht1 : t1 ∈ wtilde6_54 α N) (ht2 : t2 ∈ wtilde6_54 α N)
    (hk3 : keyW3_54 t1 < keyW3_54 t2) :
    keyW8_54 m (wtilde8Transform54 m t1) < keyW8_54 m (wtilde8Transform54 m t2) := by
  simp only [wtilde6_54, List.mem_append, List.mem_map, List.mem_finRange, true_and] at ht1 ht2
  rcases ht1 with ⟨i1, h1⟩ | ⟨j1, h1⟩ <;>
  rcases ht2 with ⟨i2, h2⟩ | ⟨j2, h2⟩
  · subst h1; subst h2
    have hi12 : i1 < i2 := by
      dsimp [keyW3_54] at hk3
      rw [lex2_lt_iff] at hk3
      rcases hk3 with h1 | ⟨_, h2⟩
      · by_contra hge
        have hle := prefSum_mono α (Fin.le_iff_val_le_val.mpr (Nat.le_of_not_lt hge))
        omega
      · exact h2
    simp only [wtilde8Transform54, i1.isLt, i2.isLt, ↓reduceIte, keyW8_54]
    exact lex2_lt_fst _ _ hi12
  · subst h1; subst h2
    have hp : prefSum54 α i1 ≤ j2.1 := by
      dsimp [keyW3_54] at hk3
      rw [lex2_lt_iff] at hk3
      rcases hk3 with h1 | ⟨h1, _⟩
      · exact le_of_lt h1
      · exact le_of_eq h1
    have hsp := modeOf_spec α hN j2.isLt
    dsimp only at hsp
    have hi1_lt_mod : i1.1 ≤ modeOf54 α j2.1 := by
      by_contra hgt
      have hlt : ⟨modeOf54 α j2.1, modeOf_lt α hN j2.isLt⟩ < i1 :=
        Fin.lt_def.mpr (Nat.lt_of_not_ge hgt)
      have := prefSum_mono α (le_of_lt hlt)
      omega
    simp only [wtilde8Transform54, i1.isLt, lt_irrefl m, ↓reduceIte, keyW8_54]
    rcases eq_or_lt_of_le hi1_lt_mod with heq | hlt
    · exfalso
      have hlt_j2 : j2.1 < prefSum54 α i1 := by
        have hlt_orig := hsp.2
        rwa [show (⟨modeOf54 α j2.1, modeOf_lt α hN j2.isLt⟩ : Fin m) = i1 from
          Fin.ext heq.symm] at hlt_orig
      omega
    · exact lex2_lt_fst _ _ hlt
  · subst h1; subst h2
    have hj_lt : j1.1 < prefSum54 α i2 := by
      dsimp [keyW3_54] at hk3
      rw [lex2_lt_iff] at hk3
      rcases hk3 with h1 | ⟨_, h2⟩
      · exact h1
      · exfalso; have := i2.isLt; omega
    have hsp := modeOf_spec α hN j1.isLt
    dsimp only at hsp
    have hmod_le : modeOf54 α j1.1 ≤ i2.1 := by
      by_contra hgt
      have hlt : i2 < ⟨modeOf54 α j1.1, modeOf_lt α hN j1.isLt⟩ :=
        Fin.lt_def.mpr (Nat.lt_of_not_ge hgt)
      have := exclPrefSum_le_prefSum_of_lt α hlt
      omega
    simp only [wtilde8Transform54, lt_irrefl m, i2.isLt, ↓reduceIte, keyW8_54]
    rcases eq_or_lt_of_le hmod_le with heq | hlt
    · exact (lex2_lt_iff _ _ _ _).mpr (Or.inr ⟨heq, lex2_lt_fst _ _ (by norm_num)⟩)
    · exact lex2_lt_fst _ _ hlt
  · subst h1; subst h2
    have hj12 : j1.1 < j2.1 := by
      dsimp [keyW3_54] at hk3
      rw [lex2_lt_iff] at hk3
      rcases hk3 with h1 | ⟨_, h2⟩
      · exact h1
      · exact absurd h2 (lt_irrefl m)
    have hsp1 := modeOf_spec α hN j1.isLt
    have hsp2 := modeOf_spec α hN j2.isLt
    dsimp only at hsp1 hsp2
    have hmod_le : modeOf54 α j1.1 ≤ modeOf54 α j2.1 := by
      by_contra hgt
      have hlt : (⟨modeOf54 α j2.1, modeOf_lt α hN j2.isLt⟩ : Fin m) <
          ⟨modeOf54 α j1.1, modeOf_lt α hN j1.isLt⟩ :=
        Fin.lt_def.mpr (Nat.lt_of_not_ge hgt)
      have := exclPrefSum_le_prefSum_of_lt α hlt
      omega
    simp only [wtilde8Transform54, lt_irrefl m, ↓reduceIte, keyW8_54]
    rcases eq_or_lt_of_le hmod_le with heq | hlt
    · exact (lex2_lt_iff _ _ _ _).mpr (Or.inr ⟨heq, lex2_lt_snd _ hj12⟩)
    · exact lex2_lt_fst _ _ hlt

theorem wtilde8_keyW8_strict {m : ℕ} (α : Fin m → ℕ) {N : ℕ} (hN : ∑ j : Fin m, α j = N) :
    ((wtilde8_54 α N).map (keyW8_54 m)).Pairwise (· < ·) := by
  set S := (wtilde6_54 α N).mergeSort (fun x y => decide (keyW3_54 x ≤ keyW3_54 y))
  have hperm : List.Perm S (wtilde6_54 α N) := List.mergeSort_perm _ _
  have hS_nd : (S.map keyW3_54).Nodup := hperm.map keyW3_54 |>.nodup_iff.mpr (wtilde6_keyW3_nodup α N)
  have hsorted : S.Pairwise (fun x y => keyW3_54 x ≤ keyW3_54 y) := pairwise_le_mergeSort keyW3_54 (wtilde6_54 α N)
  have hlt : S.Pairwise (fun x y => keyW3_54 x < keyW3_54 y) :=
    pairwise_lt_of_pairwise_le_of_nodup keyW3_54 S hS_nd hsorted
  have hmem : ∀ x ∈ S, x ∈ wtilde6_54 α N := fun x hx => hperm.mem_iff.mp hx
  have hpw : S.Pairwise (fun x y => keyW8_54 m (wtilde8Transform54 m x) < keyW8_54 m (wtilde8Transform54 m y)) := by
    refine List.Pairwise.imp_of_mem ?_ hlt
    intro a b ha hb hab
    exact keyW8_order_aux α hN a b (hmem a ha) (hmem b hb) hab
  dsimp only [wtilde8_54]
  rw [List.map_map, List.pairwise_map]
  exact hpw

theorem wtilde8_sort_by_keyW2 {m : ℕ} (α : Fin m → ℕ) (N : ℕ) :
    (wtilde8_54 α N).mergeSort (fun x y => decide (keyW2_54 x ≤ keyW2_54 y)) = wtildef_54 α N := by
  have hperm1 : List.Perm ((wtilde6_54 α N).mergeSort (fun x y => decide (keyW3_54 x ≤ keyW3_54 y)))
      (wtilde6_54 α N) := List.mergeSort_perm _ _
  have hperm2 : List.Perm (wtilde8_54 α N) ((wtilde6_54 α N).map (wtilde8Transform54 m)) :=
    hperm1.map (wtilde8Transform54 m)
  have hmap_eq : (wtilde6_54 α N).map (wtilde8Transform54 m) = wtildef_54 α N := by
    dsimp only [wtilde6_54, wtildef_54]
    rw [List.map_append, List.map_map, List.map_map]
    congr 1
    · refine List.map_congr_left fun i _ => ?_
      simp [wtilde8Transform54, i.isLt]
    · refine List.map_congr_left fun j _ => ?_
      simp [wtilde8Transform54]
  have hperm : List.Perm ((wtilde8_54 α N).mergeSort (fun x y => decide (keyW2_54 x ≤ keyW2_54 y)))
      (wtildef_54 α N) := (List.mergeSort_perm _ _).trans (hperm2.trans (by rw [hmap_eq]))
  have hsorted1 : ((wtilde8_54 α N).mergeSort (fun x y => decide (keyW2_54 x ≤ keyW2_54 y))).Pairwise
      (fun x y => keyW2_54 x ≤ keyW2_54 y) := pairwise_le_mergeSort keyW2_54 (wtilde8_54 α N)
  have hsorted2 : (wtildef_54 α N).Pairwise (fun x y => keyW2_54 x ≤ keyW2_54 y) := by
    dsimp only [wtildef_54]
    rw [List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.pairwise_map]
      exact (pairwise_finRange_lt m).imp fun {i j} hij => by
        dsimp only [Function.comp_def, keyW2_54]
        exact le_of_lt (lex2_lt_fst 0 0 (Fin.lt_def.mp hij))
    · rw [List.pairwise_map]
      exact (pairwise_finRange_lt N).imp fun {i j} hij => by
        dsimp only [Function.comp_def, keyW2_54]
        exact le_of_lt (lex2_lt_snd m (Fin.lt_def.mp hij))
    · intro x hx y hy
      simp only [List.mem_map, List.mem_finRange, true_and] at hx hy
      rcases hx with ⟨i, rfl⟩
      rcases hy with ⟨j, rfl⟩
      exact le_of_lt (lex2_lt_fst _ _ i.isLt)
  have hinj : ∀ x ∈ wtildef_54 α N, ∀ y ∈ wtildef_54 α N, keyW2_54 x = keyW2_54 y → x = y := by
    intro x hx y hy hxy
    simp only [wtildef_54, List.mem_append, List.mem_map, List.mem_finRange, true_and] at hx hy
    rcases hx with ⟨i1, rfl⟩ | ⟨j1, rfl⟩ <;>
    rcases hy with ⟨i2, rfl⟩ | ⟨j2, rfl⟩
    · have hfst := congrArg (fun p : ℕ ×ₗ ℕ => (ofLex p).1) hxy
      dsimp [keyW2_54] at hfst; rw [hfst]
    · have hfst := congrArg (fun p : ℕ ×ₗ ℕ => (ofLex p).1) hxy
      dsimp [keyW2_54] at hfst; exfalso; have := i1.isLt; omega
    · have hfst := congrArg (fun p : ℕ ×ₗ ℕ => (ofLex p).1) hxy
      dsimp [keyW2_54] at hfst; exfalso; have := i2.isLt; omega
    · have hsnd := congrArg (fun p : ℕ ×ₗ ℕ => (ofLex p).2) hxy
      dsimp [keyW2_54] at hsnd; rw [hsnd]
  exact perm_eq_of_sorted_of_inj keyW2_54 _ _ hperm hsorted1 hsorted2 hinj

lemma modeOf_mono {m : ℕ} (α : Fin m → ℕ) : Monotone (modeOf54 α) := by
  intro c₁ c₂ hc
  dsimp only [modeOf54]
  refine Finset.card_le_card fun r hr => ?_
  rw [Finset.mem_filter] at hr ⊢
  exact ⟨hr.1, le_trans hr.2 hc⟩


/-! ### Additional `Sec5` Bridges (`wtilde8_pos_spec`, `wtilde2_sort_prefix`, `wtildef_sort_prefix`) -/

lemma wtildef54_length {m : ℕ} (α : Fin m → ℕ) (N : ℕ) : (wtildef_54 α N).length = m + N := by
  simp [wtildef_54]

lemma wtilde854_length {m : ℕ} (α : Fin m → ℕ) (N : ℕ) : (wtilde8_54 α N).length = m + N := by
  have hp : ((wtilde8_54 α N).mergeSort (fun x y => decide (keyW2_54 x ≤ keyW2_54 y))).Perm
      (wtilde8_54 α N) := List.mergeSort_perm _ _
  rw [← hp.length_eq, wtilde8_sort_by_keyW2, wtildef54_length]

lemma wtilde8_pos_spec_54 {m : ℕ} (α : Fin m → ℕ) {N : ℕ} (hN : ∑ j : Fin m, α j = N)
    (pos : ℕ) (hpos : pos < (wtilde8_54 α N).length) :
    let t := (wtilde8_54 α N)[pos]
    (t.1 < m → ∃ hi : t.1 < m, t = (t.1, t.1, 0) ∧ pos ≥ t.1 ∧ pos - t.1 = prefSum54 α ⟨t.1, hi⟩) ∧
    (t.1 = m → t.2.2 < N ∧ t = (m, modeOf54 α t.2.2, t.2.2)) := by
  intro t
  set S8 := wtilde8_54 α N
  have hperm : S8.Perm (wtildef_54 α N) := by
    have hp := List.mergeSort_perm S8 (fun x y => decide (keyW2_54 x ≤ keyW2_54 y))
    rw [wtilde8_sort_by_keyW2] at hp
    exact hp.symm
  have ht_mem : t ∈ wtildef_54 α N := hperm.mem_iff.mp (List.getElem_mem hpos)
  have ht_cases := ht_mem
  simp only [wtildef_54, List.mem_append, List.mem_map, List.mem_finRange, true_and] at ht_cases
  constructor
  · intro hm
    rcases ht_cases with ⟨i, hi⟩ | ⟨j, hj⟩
    · have ha : t.1 = i.1 := by rw [← hi]
      have ht_eq : t = (t.1, t.1, 0) := by
        rw [← hi]
      have hpw : S8.Pairwise (fun x y => keyW8_54 m x < keyW8_54 m y) := by
        simpa [List.pairwise_map] using wtilde8_keyW8_strict α hN
      have htake : S8.filter (fun u => decide (keyW8_54 m u < keyW8_54 m t)) = S8.take pos := by
        have hdrop_eq : S8.drop pos = t :: S8.drop (pos + 1) := by
          rw [← List.drop_eq_getElem_cons hpos]
        have hsplit : S8 = S8.take pos ++ t :: S8.drop (pos + 1) := by
          rw [← hdrop_eq, List.take_append_drop]
        conv_lhs => rw [hsplit]
        rw [List.filter_append, List.filter_cons]
        have hleft : (S8.take pos).filter (fun u => decide (keyW8_54 m u < keyW8_54 m t)) = S8.take pos := by
          rw [List.filter_eq_self]
          intro u hu
          simp only [decide_eq_true_eq]
          rcases List.getElem_of_mem hu with ⟨j, hj, rfl⟩
          have hj_len : j < pos := by
            have := List.length_take_le pos S8
            omega
          have hj_S : j < S8.length := by omega
          rw [List.getElem_take]
          exact (List.pairwise_iff_getElem.mp hpw) j pos hj_S hpos hj_len
        have ht_not : decide (keyW8_54 m t < keyW8_54 m t) = false := decide_eq_false (lt_irrefl _)
        have hright : (S8.drop (pos + 1)).filter (fun u => decide (keyW8_54 m u < keyW8_54 m t)) = [] := by
          rw [List.filter_eq_nil_iff]
          intro u hu
          rcases List.getElem_of_mem hu with ⟨j, hj, rfl⟩
          have hlen_drop : (S8.drop (pos + 1)).length = S8.length - (pos + 1) := List.length_drop
          have hj_S : pos + 1 + j < S8.length := by omega
          rw [List.getElem_drop]
          have hgt : keyW8_54 m t < keyW8_54 m S8[pos + 1 + j] :=
            (List.pairwise_iff_getElem.mp hpw) pos (pos + 1 + j) hpos hj_S (by omega)
          simp only [decide_eq_true_eq]
          exact not_lt_of_gt hgt
        rw [hleft, ht_not, hright]
        simp
      have hpos_len : pos = ((wtildef_54 α N).filter (fun u => decide (keyW8_54 m u < keyW8_54 m t))).length := by
        rw [← (hperm.filter _).length_eq, htake, List.length_take_of_le (le_of_lt hpos)]
      have hi_eq : (⟨t.1, hm⟩ : Fin m) = i := Fin.ext ha
      rw [hpos_len, wtildef_54, List.filter_append, List.length_append]
      have hL : (((List.finRange m).map (fun r => (r.1, r.1, 0))).filter
          (fun u => decide (keyW8_54 m u < keyW8_54 m t))).length = i.1 := by
        rw [List.filter_map, List.length_map]
        have heq : (List.finRange m).filter (fun r => decide (keyW8_54 m (r.1, r.1, 0) < keyW8_54 m t)) =
            (List.finRange m).filter (fun r => decide (r.1 < i.1)) := by
          congr 1; funext r; apply decide_eq_decide.mpr
          rw [← hi]; dsimp only [keyW8_54]
          simp only [r.isLt, i.isLt, ↓reduceIte]
          rw [lex2_lt_iff]
          constructor
          · rintro (h1 | ⟨_, h2⟩)
            · exact h1
            · rw [lex2_lt_iff] at h2; omega
          · intro h1; exact Or.inl h1
        dsimp only [Function.comp_def]
        rw [heq, length_filter_finRange_lt' m i.1 (le_of_lt i.isLt)]
      have hR : (((List.finRange N).map (fun j => (m, modeOf54 α j.1, j.1))).filter
          (fun u => decide (keyW8_54 m u < keyW8_54 m t))).length = prefSum54 α i := by
        rw [List.filter_map, List.length_map]
        have heq : (List.finRange N).filter
            (fun j => decide (keyW8_54 m (m, modeOf54 α j.1, j.1) < keyW8_54 m t)) =
            (List.finRange N).filter (fun j => decide (j.1 < prefSum54 α i)) := by
          congr 1; funext j; apply decide_eq_decide.mpr
          rw [← hi]; dsimp only [keyW8_54]
          simp only [lt_irrefl m, i.isLt, ↓reduceIte]
          rw [lex2_lt_iff]
          have hsp := modeOf_spec α hN j.isLt
          dsimp only at hsp
          constructor
          · rintro (h1 | ⟨h1, _⟩)
            · have hm_lt : (⟨modeOf54 α j.1, modeOf_lt α hN j.isLt⟩ : Fin m) ≤ i :=
                Fin.le_iff_val_le_val.mpr (le_of_lt h1)
              exact lt_of_lt_of_le hsp.2 (prefSum_mono α hm_lt)
            · have hm_eq : (⟨modeOf54 α j.1, modeOf_lt α hN j.isLt⟩ : Fin m) = i := Fin.ext h1
              rw [hm_eq] at hsp
              exact hsp.2
          · intro hj_lt
            have hle_m : modeOf54 α j.1 ≤ i.1 := by
              by_contra hgt
              have hlt_i : i < ⟨modeOf54 α j.1, modeOf_lt α hN j.isLt⟩ :=
                Fin.lt_def.mpr (Nat.lt_of_not_ge hgt)
              have := exclPrefSum_le_prefSum_of_lt α hlt_i
              omega
            rcases eq_or_lt_of_le hle_m with he | hlt
            · exact Or.inr ⟨he, lex2_lt_fst _ _ (by norm_num)⟩
            · exact Or.inl hlt
        dsimp only [Function.comp_def]
        rw [heq, length_filter_finRange_lt' N (prefSum54 α i) (by rw [← hN]; exact prefSum_le_sum α i)]
      refine ⟨hm, ht_eq, ?_, ?_⟩
      · omega
      · rw [hi_eq]; omega
    · exfalso; have ha : t.1 = m := by rw [← hj]
      omega
  · intro hm
    rcases ht_cases with ⟨i, hi⟩ | ⟨j, hj⟩
    · exfalso; have ha : t.1 = i.1 := by rw [← hi]
      have := i.isLt; omega
    · rw [← hj]
      exact ⟨j.isLt, rfl⟩

private lemma sorted_prefix_perm_of_antitone {α : Type*} (L_base : List α)
    {M : ℕ} (x s_x : Fin M → α) (hM : L_base.length ≤ M)
    (hpre : ∀ (pos : ℕ) (hpos : pos < L_base.length), x ⟨pos, by omega⟩ = L_base[pos])
    (p : α → Bool)
    (hp_pre : ∀ u ∈ L_base, p u = true)
    (hp_suf : ∀ (pos : ℕ) (hpos : pos < M), L_base.length ≤ pos → p (x ⟨pos, hpos⟩) = false)
    (hperm : (List.ofFn s_x).Perm (List.ofFn x))
    (hp_anti : ∀ ⦃i j : Fin M⦄, i ≤ j → p (s_x j) = true → p (s_x i) = true) :
    ((List.ofFn s_x).take L_base.length).Perm L_base := by
  have htake_x : (List.ofFn x).take L_base.length = L_base := by
    apply List.ext_getElem
    · simp [List.length_take, Nat.min_eq_left hM]
    · intro i h1 h2
      rw [List.getElem_take, List.getElem_ofFn]
      exact hpre i h2
  have hx_filter : (List.ofFn x).filter p = L_base := by
    have hsplit : List.ofFn x = (List.ofFn x).take L_base.length ++ (List.ofFn x).drop L_base.length :=
      (List.take_append_drop _ _).symm
    conv_lhs => rw [hsplit]
    rw [List.filter_append, htake_x]
    have hL : L_base.filter p = L_base := by
      rw [List.filter_eq_self]
      intro u hu; exact hp_pre u hu
    have hR : ((List.ofFn x).drop L_base.length).filter p = [] := by
      rw [List.filter_eq_nil_iff]
      intro u hu
      rcases List.getElem_of_mem hu with ⟨j, hj, rfl⟩
      rw [List.length_drop, List.length_ofFn] at hj
      rw [List.getElem_drop, List.getElem_ofFn]
      simp [hp_suf (L_base.length + j) (by omega) (by omega)]
    rw [hL, hR, List.append_nil]
  have hs_filter_len : ((List.ofFn s_x).filter p).length = L_base.length := by
    rw [(hperm.filter p).length_eq, hx_filter]
  have hs_pre_all : ∀ (pos : ℕ) (hpos : pos < L_base.length), p (s_x ⟨pos, by omega⟩) = true := by
    intro pos hpos
    by_contra hfalse
    have hp_f : p (s_x ⟨pos, by omega⟩) = false := Bool.eq_false_iff.mpr hfalse
    have hge_f : ∀ j : Fin M, pos ≤ j.1 → p (s_x j) = false := fun j hj => by
      by_contra hjt
      have hj_t : p (s_x j) = true := Bool.eq_true_of_not_eq_false hjt
      have hle_fin : (⟨pos, by omega⟩ : Fin M) ≤ j := Fin.le_iff_val_le_val.mpr hj
      have := hp_anti hle_fin hj_t
      rw [this] at hp_f; cases hp_f
    have hs_split : List.ofFn s_x = (List.ofFn s_x).take pos ++ (List.ofFn s_x).drop pos :=
      (List.take_append_drop _ _).symm
    have hs_filter_sub : ((List.ofFn s_x).filter p).length ≤ pos := by
      rw [hs_split, List.filter_append]
      have hR_nil : ((List.ofFn s_x).drop pos).filter p = [] := by
        rw [List.filter_eq_nil_iff]
        intro u hu
        rcases List.getElem_of_mem hu with ⟨j, hj, rfl⟩
        rw [List.length_drop, List.length_ofFn] at hj
        have hlt_M : pos + j < M := by omega
        rw [List.getElem_drop, List.getElem_ofFn]
        have hfalse_j : p (s_x ⟨pos + j, hlt_M⟩) = false := hge_f ⟨pos + j, hlt_M⟩ (Nat.le_add_right pos j)
        simp [hfalse_j]
      rw [hR_nil, List.append_nil]
      exact le_trans (List.length_filter_le _ _) (List.length_take_le pos _)
    omega
  have hs_filter_eq : (List.ofFn s_x).filter p = (List.ofFn s_x).take L_base.length := by
    have hs_split : List.ofFn s_x =
        (List.ofFn s_x).take L_base.length ++ (List.ofFn s_x).drop L_base.length :=
      (List.take_append_drop _ _).symm
    have htake_filter : ((List.ofFn s_x).take L_base.length).filter p =
        (List.ofFn s_x).take L_base.length := by
      rw [List.filter_eq_self]
      intro u hu
      rcases List.getElem_of_mem hu with ⟨j, hj, rfl⟩
      have hj_len : j < L_base.length := by
        have := List.length_take_le L_base.length (List.ofFn s_x)
        omega
      rw [List.getElem_take, List.getElem_ofFn]
      exact hs_pre_all j hj_len
    have hdrop_nil : ((List.ofFn s_x).drop L_base.length).filter p = [] := by
      rw [← List.length_eq_zero_iff]
      have hlen_sum : ((List.ofFn s_x).filter p).length =
          ((List.ofFn s_x).take L_base.length).length +
          (((List.ofFn s_x).drop L_base.length).filter p).length := by
        conv_lhs => rw [hs_split, List.filter_append, List.length_append, htake_filter]
      rw [hs_filter_len, List.length_take_of_le (by simp [hM])] at hlen_sum
      omega
    conv_lhs => rw [hs_split, List.filter_append, htake_filter, hdrop_nil, List.append_nil]
  rw [← hs_filter_eq, ← hx_filter]
  exact hperm.filter p

lemma wtilde2_sort_prefix_54 {m : ℕ} (α : Fin m → ℕ) {N : ℕ} (hN : ∑ j : Fin m, α j = N)
    (M : ℕ) (x s_x : Fin M → Sec5Rec54) (hM : m + N ≤ M)
    (hpre : ∀ (pos : ℕ) (hpos : pos < m + N),
      x ⟨pos, by omega⟩ = (wtilde2_54 α N)[pos]'(by rw [wtilde2_length]; exact hpos))
    (hsuf : ∀ (pos : ℕ) (hpos : pos < M), m + N ≤ pos → (x ⟨pos, hpos⟩).2.2 = N + 1)
    (hperm : (List.ofFn s_x).Perm (List.ofFn x))
    (hmono : Monotone (keyW3_54 ∘ s_x)) :
    ∀ (pos : ℕ) (hpos : pos < m + N),
      s_x ⟨pos, by omega⟩ = (wtilde3_54 α N)[pos]'(by rw [wtilde3_length]; exact hpos) := by
  have hlen : (wtilde2_54 α N).length = m + N := wtilde2_length α N
  have hpref_perm : ((List.ofFn s_x).take (m + N)).Perm (wtilde2_54 α N) := by
    rw [← hlen]
    refine sorted_prefix_perm_of_antitone (wtilde2_54 α N) x s_x (by omega)
      (fun pos hpos => by rw [hlen] at hpos; exact hpre pos hpos)
      (fun u => decide (u.2.2 ≤ N))
      (fun u hu => ?_)
      (fun pos hpos hge => by simp [hsuf pos hpos (by omega)])
      hperm
      (fun i j hij h => ?_)
    · simp only [wtilde2_54, List.mem_append, List.mem_map, List.mem_finRange, true_and] at hu
      rcases hu with ⟨i, rfl⟩ | ⟨j, rfl⟩
      · exact decide_eq_true (by rw [← hN]; exact prefSum_le_sum α i)
      · exact decide_eq_true (le_of_lt j.isLt)
    · simp only [decide_eq_true_eq] at h ⊢
      have hm := hmono hij
      dsimp only [Function.comp_apply, keyW3_54] at hm
      have h1 : (s_x i).2.2 ≤ (s_x j).2.2 := by
        by_contra hlt
        have hgt : keyW3_54 (s_x j) < keyW3_54 (s_x i) :=
          lex2_lt_fst _ _ (Nat.lt_of_not_ge hlt)
        exact absurd hm (not_le_of_gt hgt)
      omega
  have hsorted_take : ((List.ofFn s_x).take (m + N)).Pairwise (fun a b => keyW3_54 a ≤ keyW3_54 b) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    rw [List.length_take_of_le (by simp [hM])] at hi hj
    rw [List.getElem_take, List.getElem_take, List.getElem_ofFn, List.getElem_ofFn]
    exact hmono (Fin.le_iff_val_le_val.mpr (le_of_lt hij))
  have hsorted_w3 : (wtilde3_54 α N).Pairwise (fun a b => keyW3_54 a ≤ keyW3_54 b) :=
    pairwise_le_mergeSort keyW3_54 (wtilde2_54 α N)
  have hinj : ∀ a ∈ wtilde3_54 α N, ∀ b ∈ wtilde3_54 α N, keyW3_54 a = keyW3_54 b → a = b := by
    have hnd : ((wtilde3_54 α N).map keyW3_54).Nodup :=
      (List.mergeSort_perm _ _).map keyW3_54 |>.nodup_iff.mpr (wtilde2_keyW3_nodup α N)
    intro a ha b hb hab
    rcases List.getElem_of_mem ha with ⟨i, hi, rfl⟩
    rcases List.getElem_of_mem hb with ⟨j, hj, rfl⟩
    have hij : i = j := by
      by_contra hne
      have hnd_get := List.nodup_iff_injective_getElem.mp hnd
      have heq_map : (⟨i, by simpa using hi⟩ : Fin ((wtilde3_54 α N).map keyW3_54).length) =
          ⟨j, by simpa using hj⟩ :=
        hnd_get (by simpa using hab)
      exact hne (congrArg Fin.val heq_map)
    subst hij; rfl
  have heq_list : (List.ofFn s_x).take (m + N) = wtilde3_54 α N :=
    perm_eq_of_sorted_of_inj keyW3_54 _ _
      (hpref_perm.trans (List.mergeSort_perm _ _).symm) hsorted_take hsorted_w3 hinj
  intro pos hpos
  have hget := congrArg (fun L : List Sec5Rec54 => L[pos]?) heq_list
  have hl1 : pos < ((List.ofFn s_x).take (m + N)).length := by
    rw [List.length_take_of_le (by simp [hM])]; exact hpos
  have hl2 : pos < (wtilde3_54 α N).length := by rw [wtilde3_length]; exact hpos
  rw [List.getElem?_eq_getElem hl1, List.getElem?_eq_getElem hl2] at hget
  have hv := Option.some.inj hget
  rw [List.getElem_take, List.getElem_ofFn] at hv
  exact hv

lemma wtildef_sort_prefix_54 {m : ℕ} (α : Fin m → ℕ) {N : ℕ} (hN : ∑ j : Fin m, α j = N)
    (M : ℕ) (x s_x : Fin M → Sec5Rec54) (hM : m + N ≤ M)
    (hpre : ∀ (pos : ℕ) (hpos : pos < m + N),
      x ⟨pos, by omega⟩ = (wtildef_54 α N)[pos]'(by rw [wtildef54_length]; exact hpos))
    (hsuf : ∀ (pos : ℕ) (hpos : pos < M), m + N ≤ pos → (x ⟨pos, hpos⟩).2.1 = m)
    (hperm : (List.ofFn s_x).Perm (List.ofFn x))
    (hmono : Monotone (keyW8_0_54 m ∘ s_x)) :
    ∀ (pos : ℕ) (hpos : pos < m + N),
      s_x ⟨pos, by omega⟩ = (wtilde8_54 α N)[pos]'(by rw [wtilde854_length]; exact hpos) := by
  have hlen : (wtildef_54 α N).length = m + N := wtildef54_length α N
  have hpref_perm : ((List.ofFn s_x).take (m + N)).Perm (wtildef_54 α N) := by
    rw [← hlen]
    refine sorted_prefix_perm_of_antitone (wtildef_54 α N) x s_x (by omega)
      (fun pos hpos => by rw [hlen] at hpos; exact hpre pos hpos)
      (fun u => decide (u.2.1 < m))
      (fun u hu => ?_)
      (fun pos hpos hge => by simp [hsuf pos hpos (by omega)])
      hperm
      (fun i j hij h => ?_)
    · simp only [wtildef_54, List.mem_append, List.mem_map, List.mem_finRange, true_and] at hu
      rcases hu with ⟨i, rfl⟩ | ⟨j, rfl⟩
      · exact decide_eq_true i.isLt
      · exact decide_eq_true (modeOf_lt α hN j.isLt)
    · simp only [decide_eq_true_eq] at h ⊢
      have hm := hmono hij
      dsimp only [Function.comp_apply, keyW8_0_54] at hm
      have h1 : (s_x i).2.1 ≤ (s_x j).2.1 := by
        by_contra hlt
        have hgt : keyW8_0_54 m (s_x j) < keyW8_0_54 m (s_x i) :=
          lex2_lt_fst _ _ (Nat.lt_of_not_ge hlt)
        exact absurd hm (not_le_of_gt hgt)
      omega
  have hw8_perm : (wtilde8_54 α N).Perm (wtildef_54 α N) := by
    have hp := List.mergeSort_perm (wtilde8_54 α N) (fun x y => decide (keyW2_54 x ≤ keyW2_54 y))
    rw [wtilde8_sort_by_keyW2] at hp
    exact hp.symm
  have hkey_eq_w8 : ∀ u ∈ wtilde8_54 α N, keyW8_0_54 m u = keyW8_54 m u := by
    intro u hu
    have hu' := hw8_perm.mem_iff.mp hu
    simp only [wtildef_54, List.mem_append, List.mem_map, List.mem_finRange, true_and] at hu'
    rcases hu' with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · simp [keyW8_0_54, keyW8_54]
    · simp [keyW8_0_54, keyW8_54]
  have hsorted_take : ((List.ofFn s_x).take (m + N)).Pairwise (fun a b => keyW8_0_54 m a ≤ keyW8_0_54 m b) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    rw [List.length_take_of_le (by simp [hM])] at hi hj
    rw [List.getElem_take, List.getElem_take, List.getElem_ofFn, List.getElem_ofFn]
    exact hmono (Fin.le_iff_val_le_val.mpr (le_of_lt hij))
  have hpw8 : (wtilde8_54 α N).Pairwise (fun a b => keyW8_54 m a < keyW8_54 m b) := by
    simpa [List.pairwise_map] using wtilde8_keyW8_strict α hN
  have hsorted_w8 : (wtilde8_54 α N).Pairwise (fun a b => keyW8_0_54 m a ≤ keyW8_0_54 m b) := by
    refine List.Pairwise.imp_of_mem ?_ hpw8
    intro a b ha hb hab
    rw [hkey_eq_w8 a ha, hkey_eq_w8 b hb]
    exact le_of_lt hab
  have hinj : ∀ a ∈ wtilde8_54 α N, ∀ b ∈ wtilde8_54 α N, keyW8_0_54 m a = keyW8_0_54 m b → a = b := by
    have hpw0 : (wtilde8_54 α N).Pairwise (fun a b => keyW8_0_54 m a < keyW8_0_54 m b) := by
      refine List.Pairwise.imp_of_mem ?_ hpw8
      intro a b ha hb hab
      rwa [hkey_eq_w8 a ha, hkey_eq_w8 b hb]
    have hnd : ((wtilde8_54 α N).map (keyW8_0_54 m)).Nodup := by
      rw [List.nodup_iff_pairwise_ne]
      rw [List.pairwise_map]
      exact hpw0.imp fun h => ne_of_lt h
    intro a ha b hb hab
    rcases List.getElem_of_mem ha with ⟨i, hi, rfl⟩
    rcases List.getElem_of_mem hb with ⟨j, hj, rfl⟩
    have hij : i = j := by
      by_contra hne
      have hnd_get := List.nodup_iff_injective_getElem.mp hnd
      have heq_map : (⟨i, by simpa using hi⟩ : Fin ((wtilde8_54 α N).map (keyW8_0_54 m)).length) =
          ⟨j, by simpa using hj⟩ :=
        hnd_get (by simpa using hab)
      exact hne (congrArg Fin.val heq_map)
    subst hij; rfl
  have heq_list : (List.ofFn s_x).take (m + N) = wtilde8_54 α N :=
    perm_eq_of_sorted_of_inj (keyW8_0_54 m) _ _
      (hpref_perm.trans hw8_perm.symm) hsorted_take hsorted_w8 hinj
  intro pos hpos
  have hget := congrArg (fun L : List Sec5Rec54 => L[pos]?) heq_list
  have hl1 : pos < ((List.ofFn s_x).take (m + N)).length := by
    rw [List.length_take_of_le (by simp [hM])]; exact hpos
  have hl2 : pos < (wtilde8_54 α N).length := by rw [wtilde854_length]; exact hpos
  rw [List.getElem?_eq_getElem hl1, List.getElem?_eq_getElem hl2] at hget
  have hv := Option.some.inj hget
  rw [List.getElem_take, List.getElem_ofFn] at hv
  exact hv

lemma permMat_id {ι : Type*} [DecidableEq ι] : permMat (id : ι → ι) = 1 := by
  ext y z
  simp [permMat, Matrix.one_apply]

lemma permMat_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (f g : ι → ι) :
    permMat f * permMat g = permMat (f ∘ g) := by
  ext y z
  simp only [Matrix.mul_apply, permMat, Matrix.of_apply, Function.comp_apply]
  rw [Finset.sum_eq_single (g z)]
  · simp
  · intro x _ hx; simp [hx]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma seqClean_perm {main anc₁ anc₂ : ℕ}
    (lc₁ : LayeredCircuit (main + anc₁)) (lc₂ : LayeredCircuit (main + anc₂))
    {f g : Qubits main → Qubits main}
    (h₁ : lc₁.ImplementsOnClean (permMat f)) (h₂ : lc₂.ImplementsOnClean (permMat g)) :
    (seqClean lc₁ lc₂).ImplementsOnClean (permMat (g ∘ f)) := by
  have h := seqClean_implements lc₁ lc₂ (permMat f) (permMat g) h₁ h₂
  rwa [permMat_mul] at h

lemma adj_implementsOnClean_perm {main anc : ℕ} (lc : LayeredCircuit (main + anc))
    {f g : Qubits main → Qubits main}
    (_hleft : ∀ x, g (f x) = x) (hright : ∀ x, f (g x) = x)
    (hlc : lc.ImplementsOnClean (permMat f)) :
    lc.adj.ImplementsOnClean (permMat g) := by
  apply implementsOnClean_of_act_perm
  intro x
  have hfg := act_ket_of_implementsOnClean_perm hlc (g x)
  rw [hright x] at hfg
  have hadj := congrArg (act lc.adj.unitary) hfg.symm
  conv_rhs at hadj =>
    rw [← act_mul, LayeredCircuit.adj_unitary,
      Matrix.mem_unitaryGroup_iff'.mp lc.unitary_mem_unitaryGroup, act_one]
  exact hadj

lemma implementsOnClean_id_perm {main anc : ℕ} :
    (LayeredCircuit.id (main + anc)).ImplementsOnClean (permMat id) := by
  apply implementsOnClean_of_act_perm
  intro x; simp [LayeredCircuit.id_unitary, act_one]

lemma act_mapWires_perm {main anc m : ℕ} (lc : LayeredCircuit (main + anc))
    (f : Qubits main → Qubits main) (hlc : lc.ImplementsOnClean (permMat f))
    (emb : Fin (main + anc) ↪ Fin m) (z : Qubits m)
    (hclean : ∀ j : Fin anc, z (emb (Fin.natAdd main j)) = false) :
    let embMain : Fin main ↪ Fin m := (Fin.castAddEmb anc).trans emb
    act (lc.mapWires emb).unitary (ket z) = ket (updateOn embMain z (f (z ∘ embMain))) := by
  intro embMain
  have h := act_mapWires_implementsOnClean lc (permMat f) hlc emb z hclean
  dsimp only at h
  dsimp only [embMain]
  rw [h, Finset.sum_eq_single (f (z ∘ ((Fin.castAddEmb anc).trans emb)))]
  · simp [permMat]
  · intro y _ hy; simp [permMat, hy]
  · intro hmem; exact absurd (Finset.mem_univ _) hmem

@[simp] lemma padZero_val_lt {main anc : ℕ} (x : Qubits main) (u : Fin (main + anc)) (h : u.1 < main) :
    padZero main anc x u = x ⟨u.1, h⟩ := by
  have heq : u = Fin.castAdd anc ⟨u.1, h⟩ := Fin.ext rfl
  conv_lhs => rw [heq]
  exact padZero_castAdd main anc x ⟨u.1, h⟩

@[simp] lemma padZero_val_ge {main anc : ℕ} (x : Qubits main) (u : Fin (main + anc)) (h : main ≤ u.1) :
    padZero main anc x u = false := by
  have heq : u = Fin.natAdd main ⟨u.1 - main, by have := u.isLt; omega⟩ := by
    apply Fin.ext; simp; omega
  conv_lhs => rw [heq]
  exact padZero_natAdd main anc x ⟨u.1 - main, by have := u.isLt; omega⟩

@[simp] lemma padZero_zero {main : ℕ} (x : Qubits main) (u : Fin (main + 0)) :
    padZero main 0 x u = x ⟨u.1, by have := u.isLt; omega⟩ :=
  padZero_val_lt x u (by have := u.isLt; omega)

lemma bitsToNatLSB_rev {q : ℕ} (b : Qubits q) :
    bitsToNatLSB (fun j : Fin q => b j.rev) = bitsToNat b := by
  dsimp only [bitsToNatLSB, bitsToNat]
  refine Fintype.sum_equiv (Fin.revPerm : Equiv.Perm (Fin q)) _ _ fun i => ?_
  simp only [Fin.revPerm_apply, Fin.val_rev]
  have hi := i.isLt
  have heq : i.1 = q - 1 - (q - (i.1 + 1)) := by omega
  rw [← heq]

lemma natToBits_eq_rev_natToBitsLSB (q k : ℕ) (hk : k < 2 ^ q) :
    (fun j : Fin q => natToBits q k j.rev) = natToBitsLSB q k := by
  have hbits : bitsToNat (natToBits q k) = k := by
    rw [← bitsEquivFin_apply]
    simp [natToBits, Nat.mod_eq_of_lt hk]
  have hrev : bitsToNatLSB (fun j : Fin q => natToBits q k j.rev) = k := by
    rw [bitsToNatLSB_rev, hbits]
  rw [← natToBitsLSB_bitsToNatLSB (fun j : Fin q => natToBits q k j.rev), hrev]

lemma natToBits_apply {q k : ℕ} (hk : k < 2 ^ q) (i : Fin q) :
    natToBits q k i = natToBitsLSB q k i.rev := by
  have h := congrFun (natToBits_eq_rev_natToBitsLSB q k hk) i.rev
  simpa [Fin.rev_rev] using h

lemma bitsToNatLSB_all_false (w : ℕ) : bitsToNatLSB (fun _ : Fin w => false) = 0 := by
  simp [bitsToNatLSB]


private def copyPrefixCircuit (w : ℕ) : (k : ℕ) → k ≤ w → LayeredCircuit (w + w)
  | 0, _ => LayeredCircuit.id (w + w)
  | k + 1, hk =>
    let prev := copyPrefixCircuit w k (by omega)
    let c : Fin (w + w) := ⟨k, by omega⟩
    let t : Fin (w + w) := ⟨w + k, by omega⟩
    have hct : c ≠ t := Fin.ne_of_val_ne (by dsimp [c, t]; omega)
    prev.seq (cnotGate c t hct)

private lemma copyPrefixCircuit_size (w k : ℕ) (hk : k ≤ w) :
    (copyPrefixCircuit w k hk).size = k := by
  induction k with
  | zero => simp [copyPrefixCircuit]
  | succ k ih => simp [copyPrefixCircuit, ih (by omega)]

private lemma act_copyPrefixCircuit_ket (w k : ℕ) (hk : k ≤ w) (z : Qubits (w + w)) :
    act (copyPrefixCircuit w k hk).unitary (ket z) =
      ket (fun u => if h : w ≤ u.1 ∧ u.1 < w + k then
        xor (z u) (z ⟨u.1 - w, by omega⟩) else z u) := by
  induction k with
  | zero =>
    simp only [copyPrefixCircuit, LayeredCircuit.id_unitary, act_one]
    congr 1; funext u; rw [dif_neg (by omega)]
  | succ k ih =>
    dsimp only [copyPrefixCircuit]
    rw [LayeredCircuit.seq_unitary, act_mul, ih (by omega), act_cnotGate_ket]
    congr 1; funext u
    let c : Fin (w + w) := ⟨k, by omega⟩
    let t : Fin (w + w) := ⟨w + k, by omega⟩
    by_cases hut : u = t
    · subst hut
      have ht_new : w ≤ t.1 ∧ t.1 < w + (k + 1) := by dsimp [t]; omega
      rw [Function.update_self, dif_pos ht_new]
      have hnc : ¬ (w ≤ c.1 ∧ c.1 < w + k) := by dsimp [c]; omega
      have hnt : ¬ (w ≤ t.1 ∧ t.1 < w + k) := by dsimp [t]; omega
      rw [dif_neg hnc, dif_neg hnt]
      have hsub : (⟨t.1 - w, by omega⟩ : Fin (w + w)) = c := Fin.ext (by simp [c, t])
      rw [hsub]
    · rw [Function.update_of_ne hut]
      by_cases hu : w ≤ u.1 ∧ u.1 < w + k
      · have hu' : w ≤ u.1 ∧ u.1 < w + (k + 1) := by omega
        rw [dif_pos hu, dif_pos hu']
      · have hu' : ¬ (w ≤ u.1 ∧ u.1 < w + (k + 1)) := by
          intro h; apply hu; refine ⟨h.1, ?_⟩
          by_contra hge
          apply hut; apply Fin.ext; dsimp [t]; omega
        rw [dif_neg hu, dif_neg hu']

/-- Bitwise XOR copy `(a, b) ↦ (a, b ^^^ a)` using `w` CNOT gates (`0` ancillas). -/
def copyRegCircuit (w : ℕ) : LayeredCircuit ((w + w) + 0) :=
  copyPrefixCircuit w w le_rfl

@[simp] lemma copyRegCircuit_size (w : ℕ) : (copyRegCircuit w).size = w :=
  copyPrefixCircuit_size w w le_rfl

def copyRegFn (w : ℕ) (x : Qubits (w + w)) : Qubits (w + w) :=
  fun u => if h : w ≤ u.1 then xor (x u) (x ⟨u.1 - w, by omega⟩) else x u

lemma copyRegCircuit_implements (w : ℕ) :
    (copyRegCircuit w).ImplementsOnClean (permMat (copyRegFn w)) := by
  apply implementsOnClean_of_act_perm
  intro x
  dsimp only [copyRegCircuit]
  have h0 : padZero (w + w) 0 x = x := by
    funext u; simp
  rw [h0, act_copyPrefixCircuit_ket]
  congr 1; funext u
  have hu := u.isLt
  by_cases hw : w ≤ u.1
  · simp [copyRegFn, hw, show u.1 < w + w by omega]
  · simp [copyRegFn, hw]


private def setConstPrefixCircuit (w c : ℕ) : (k : ℕ) → k ≤ w → LayeredCircuit w
  | 0, _ => LayeredCircuit.id w
  | k + 1, hk =>
    let prev := setConstPrefixCircuit w c k (by omega)
    if c.testBit k then prev.seq (pauliXGate ⟨k, by omega⟩) else prev

private lemma setConstPrefixCircuit_size (w c k : ℕ) (hk : k ≤ w) :
    (setConstPrefixCircuit w c k hk).size ≤ k := by
  induction k with
  | zero => simp [setConstPrefixCircuit]
  | succ k ih =>
    dsimp only [setConstPrefixCircuit]
    split_ifs <;> have h := ih (by omega) <;> simp <;> omega

private lemma act_setConstPrefixCircuit_ket (w c k : ℕ) (hk : k ≤ w) (z : Qubits w) :
    act (setConstPrefixCircuit w c k hk).unitary (ket z) =
      ket (fun i => if i.1 < k then xor (z i) (c.testBit i.1) else z i) := by
  induction k with
  | zero =>
    simp only [setConstPrefixCircuit, LayeredCircuit.id_unitary, act_one]
    exact congrArg ket (funext fun i => (if_neg (Nat.not_lt_zero i.1)).symm)
  | succ k ih =>
    dsimp only [setConstPrefixCircuit]
    cases hc : c.testBit k
    · rw [if_neg (by simp), ih (by omega)]
      congr 1; funext i
      by_cases hi : i.1 < k
      · rw [if_pos hi, if_pos (by omega)]
      · rw [if_neg hi]
        by_cases hk_eq : i.1 = k
        · rw [if_pos (by omega), hk_eq, hc, Bool.xor_false]
        · rw [if_neg (by omega)]
    · rw [if_pos (by simp), LayeredCircuit.seq_unitary, act_mul, ih (by omega),
        act_pauliXGate_ket]
      congr 1; funext i
      by_cases hik : i = ⟨k, by omega⟩
      · subst hik
        simp [Function.update_self, hc]
      · rw [Function.update_of_ne hik]
        have hne_v : i.1 ≠ k := fun h => hik (Fin.ext h)
        by_cases hi : i.1 < k
        · rw [if_pos hi, if_pos (by omega)]
        · rw [if_neg hi, if_neg (by omega)]

/-- XORs classical `natToBitsLSB w c` onto a `w`-qubit register (`≤ w` gates, `0` ancillas). -/
def setConstCircuit (w c : ℕ) : LayeredCircuit (w + 0) :=
  setConstPrefixCircuit w c w le_rfl

lemma setConstCircuit_size (w c : ℕ) : (setConstCircuit w c).size ≤ w :=
  setConstPrefixCircuit_size w c w le_rfl

lemma setConstCircuit_implements (w c : ℕ) :
    (setConstCircuit w c).ImplementsOnClean
      (permMat fun x : Qubits w => fun i => xor (x i) (natToBitsLSB w c i)) := by
  apply implementsOnClean_of_act_perm
  intro x
  dsimp only [setConstCircuit]
  have h0 : padZero w 0 x = x := by
    funext u; simp
  rw [h0]
  have hact := act_setConstPrefixCircuit_ket w c w le_rfl x
  change act (setConstPrefixCircuit w c w le_rfl).unitary (ket x) = _
  rw [hact]
  congr 1; funext i
  simp [natToBitsLSB, i.isLt]


private lemma multiEqCtrl1_implements_perm (L : ℕ) (pat : Qubits L) :
    (multiEqCtrl1 L pat pauliX pauliX_mem_unitaryGroup).ImplementsOnClean
      (permMat fun v : Qubits (L + 1) =>
        Function.update v ⟨L, Nat.lt_succ_self L⟩
          (xor (v ⟨L, Nat.lt_succ_self L⟩) (decide (∀ i : Fin L, v ⟨i.1, by omega⟩ = pat i)))) := by
  have h := multiEqCtrl1_implements L pat pauliX pauliX_mem_unitaryGroup
  have heq : eqCtrlMat L pat pauliX =
      permMat (fun v : Qubits (L + 1) =>
        Function.update v ⟨L, Nat.lt_succ_self L⟩
          (xor (v ⟨L, Nat.lt_succ_self L⟩) (decide (∀ i : Fin L, v ⟨i.1, by omega⟩ = pat i)))) := by
    ext y z
    simp only [eqCtrlMat, permMat, Matrix.of_apply]
    by_cases hyz : ∀ i : Fin L, y ⟨i.1, by omega⟩ = z ⟨i.1, by omega⟩
    · rw [if_pos hyz]
      by_cases hall : ∀ i : Fin L, z ⟨i.1, by omega⟩ = pat i
      · rw [if_pos hall]
        have hy_eq : (y = Function.update z ⟨L, Nat.lt_succ_self L⟩
            (xor (z ⟨L, Nat.lt_succ_self L⟩) (decide (∀ i : Fin L, z ⟨i.1, by omega⟩ = pat i)))) ↔
            y ⟨L, Nat.lt_succ_self L⟩ = !z ⟨L, Nat.lt_succ_self L⟩ := by
          simp only [decide_eq_true hall, Bool.xor_true]
          constructor
          · intro h; rw [h, Function.update_self]
          · intro h; funext k
            rcases Fin.eq_castSucc_or_eq_last k with ⟨k', rfl⟩ | rfl
            · have hne : k'.castSucc ≠ ⟨L, Nat.lt_succ_self L⟩ := Fin.ne_of_val_ne (by simp; omega)
              rw [Function.update_of_ne hne]; exact hyz k'
            · have hlast : Fin.last L = ⟨L, Nat.lt_succ_self L⟩ := rfl
              rw [hlast, Function.update_self]; exact h
        by_cases hym : y ⟨L, Nat.lt_succ_self L⟩ = !z ⟨L, Nat.lt_succ_self L⟩
        · rw [if_pos (hy_eq.mpr hym), hym]
          cases z ⟨L, Nat.lt_succ_self L⟩ <;> simp [pauliX]
        · rw [if_neg (mt hy_eq.mp hym)]
          cases hzm : z ⟨L, Nat.lt_succ_self L⟩ <;> cases hym' : y ⟨L, Nat.lt_succ_self L⟩ <;>
            simp [pauliX, hzm, hym'] at hym ⊢
      · rw [if_neg hall]
        have hy_eq : (y = Function.update z ⟨L, Nat.lt_succ_self L⟩
            (xor (z ⟨L, Nat.lt_succ_self L⟩) (decide (∀ i : Fin L, z ⟨i.1, by omega⟩ = pat i)))) ↔
            y ⟨L, Nat.lt_succ_self L⟩ = z ⟨L, Nat.lt_succ_self L⟩ := by
          simp only [decide_eq_false hall, Bool.xor_false, Function.update_eq_self]
          constructor
          · intro h; rw [h]
          · intro h; funext k
            rcases Fin.eq_castSucc_or_eq_last k with ⟨k', rfl⟩ | rfl
            · exact hyz k'
            · exact h
        by_cases hym : y ⟨L, Nat.lt_succ_self L⟩ = z ⟨L, Nat.lt_succ_self L⟩
        · rw [if_pos hym, if_pos (hy_eq.mpr hym)]
        · rw [if_neg hym, if_neg (mt hy_eq.mp hym)]
    · rw [if_neg hyz]
      symm; rw [if_neg]
      intro h; apply hyz; intro i
      have h1 := congrFun h ⟨i.1, by omega⟩
      have hne : (⟨i.1, by omega⟩ : Fin (L + 1)) ≠ ⟨L, Nat.lt_succ_self L⟩ :=
        Fin.ne_of_val_ne (by simp; omega)
      rwa [Function.update_of_ne hne] at h1
  rwa [← heq]


private def eqConstSetEmb (w : ℕ) : Fin (w + 0) ↪ Fin ((w + 1) + w) where
  toFun i := ⟨i.1, by omega⟩
  inj' a b h := Fin.ext (by have := congrArg Fin.val h; exact this)

@[simp] private lemma eqConstSetEmb_val (w : ℕ) (i : Fin (w + 0)) :
    (eqConstSetEmb w i).1 = i.1 := rfl

/-- Constant equality `(x, t) ↦ (x, t ^^^ decide (x = natToBitsLSB w c))` in `≤ 14 * w + 12` gates. -/
noncomputable def eqConstCircuit (w c : ℕ) : LayeredCircuit ((w + 1) + w) :=
  let sc := (setConstCircuit w c).mapWires (eqConstSetEmb w)
  let eqZ := multiEqCtrl1 w (fun _ => false) pauliX pauliX_mem_unitaryGroup
  sc.seq (eqZ.seq sc)

lemma eqConstCircuit_size (w c : ℕ) : (eqConstCircuit w c).size ≤ 14 * w + 12 := by
  dsimp only [eqConstCircuit]
  simp only [LayeredCircuit.seq_size, LayeredCircuit.mapWires_size]
  have h1 := setConstCircuit_size w c
  have h2 := multiEqCtrl1_size w (fun _ => false) pauliX pauliX_mem_unitaryGroup
  omega

def eqConstFn (w c : ℕ) (x : Qubits (w + 1)) : Qubits (w + 1) :=
  Function.update x ⟨w, by omega⟩
    (xor (x ⟨w, by omega⟩)
      (decide (∀ i : Fin w, x ⟨i.1, by omega⟩ = natToBitsLSB w c i)))

lemma eqConstCircuit_implements (w c : ℕ) :
    (eqConstCircuit w c).ImplementsOnClean (permMat (eqConstFn w c)) := by
  apply implementsOnClean_of_act_perm
  intro x
  let z0 := padZero (w + 1) w x
  let tgt : Fin ((w + 1) + w) := ⟨w, by omega⟩
  let sc := (setConstCircuit w c).mapWires (eqConstSetEmb w)
  let eqZ := multiEqCtrl1 w (fun _ => false) pauliX pauliX_mem_unitaryGroup
  let pat := natToBitsLSB w c
  let z1 : Qubits ((w + 1) + w) := fun u =>
    if h : u.1 < w then xor (z0 u) (pat ⟨u.1, h⟩) else z0 u
  have h1 : act sc.unitary (ket z0) = ket z1 := by
    have hact := act_mapWires_perm (setConstCircuit w c) _ (setConstCircuit_implements w c)
      (eqConstSetEmb w) z0 (fun j => Fin.elim0 j)
    rw [hact]; congr 1; funext u
    by_cases hu : u.1 < w
    · have hu_eq : u = ((Fin.castAddEmb 0).trans (eqConstSetEmb w)) ⟨u.1, hu⟩ := Fin.ext rfl
      rw [hu_eq, updateOn_apply_emb]
      simp [Function.comp_apply, z1, pat, hu, Fin.castAddEmb]
    · have hnot : u ∉ Set.range ((Fin.castAddEmb 0).trans (eqConstSetEmb w)) := by
        rintro ⟨j, hj⟩; have := congrArg Fin.val hj; simp at this; omega
      rw [updateOn_apply_not_mem _ _ _ hnot]
      simp [z1, hu]
  have hclean_z1 : ∀ j : Fin w, z1 (Fin.natAdd (w + 1) j) = false := fun j => by
    dsimp only [z1]; rw [dif_neg (by simp; omega)]; exact padZero_natAdd (w + 1) w x j
  have hz1_w : z1 tgt = x ⟨w, by omega⟩ := by
    dsimp only [z1]; rw [dif_neg (by dsimp [tgt]; omega)]
    exact padZero_val_lt x tgt (by dsimp [tgt]; omega)
  let z2 := Function.update z1 tgt (xor (z1 tgt) (decide (∀ i : Fin w, x ⟨i.1, by omega⟩ = pat i)))
  have h2 : act eqZ.unitary (ket z1) = ket z2 := by
    have hact := act_ket_of_implementsOnClean_perm (multiEqCtrl1_implements_perm w (fun _ => false))
      (fun i : Fin (w + 1) => z1 (Fin.castAdd w i))
    have hz1_eq : z1 = padZero (w + 1) w (fun i : Fin (w + 1) => z1 (Fin.castAdd w i)) := by
      funext u; refine Fin.addCases (fun i => ?_) (fun j => ?_) u
      · simp
      · simp [hclean_z1 j]
    rw [← hz1_eq] at hact
    rw [hact]; congr 1; funext u
    have hall_iff : (∀ i : Fin w, z1 (Fin.castAdd w ⟨i.1, by omega⟩) = false) ↔
        (∀ i : Fin w, x ⟨i.1, by omega⟩ = pat i) := by
      refine forall_congr' fun i => ?_
      dsimp only [z1, z0]
      have hflt : (Fin.castAdd w (⟨i.1, by omega⟩ : Fin (w + 1))).1 < w := by simp
      rw [dif_pos hflt, padZero_val_lt x _ (by omega)]
      have hsub : (⟨(Fin.castAdd w (⟨i.1, by omega⟩ : Fin (w + 1))).1, hflt⟩ : Fin w) = i := rfl
      have hsub2 : (⟨(Fin.castAdd w (⟨i.1, by omega⟩ : Fin (w + 1))).1, by omega⟩ : Fin (w + 1)) =
          ⟨i.1, by omega⟩ := rfl
      rw [hsub, hsub2]
      cases x ⟨i.1, by omega⟩ <;> cases pat i <;> simp
    have hdec : decide (∀ i : Fin w, z1 (Fin.castAdd w ⟨i.1, by omega⟩) = false) =
        decide (∀ i : Fin w, x ⟨i.1, by omega⟩ = pat i) := by
      rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; exact hall_iff
    by_cases hu_lt : u.1 < w + 1
    · rw [padZero_val_lt _ u hu_lt]
      by_cases huw : u.1 = w
      · have hut : u = tgt := Fin.ext huw
        subst hut
        have hi_eq : (⟨tgt.1, hu_lt⟩ : Fin (w + 1)) = ⟨w, Nat.lt_succ_self w⟩ := Fin.ext rfl
        rw [hi_eq, Function.update_self]
        dsimp only [z2]; rw [Function.update_self, hdec]
        rfl
      · have hut : u ≠ tgt := Fin.ne_of_val_ne huw
        have hne_x : (⟨u.1, hu_lt⟩ : Fin (w + 1)) ≠ ⟨w, Nat.lt_succ_self w⟩ :=
          Fin.ne_of_val_ne huw
        rw [Function.update_of_ne hne_x]
        dsimp only [z2]; rw [Function.update_of_ne hut]
        congr 1
    · have hge : w + 1 ≤ u.1 := by omega
      have hut : u ≠ tgt := Fin.ne_of_val_ne (by dsimp [tgt]; omega)
      rw [padZero_val_ge _ u hge]
      have hu_eq : u = Fin.natAdd (w + 1) ⟨u.1 - (w + 1), by have := u.isLt; omega⟩ :=
        Fin.ext (by simp; omega)
      dsimp only [z2]; rw [Function.update_of_ne hut, hu_eq, hclean_z1]
  have h3 : act sc.unitary (ket z2) = ket (padZero (w + 1) w (eqConstFn w c x)) := by
    have hact := act_mapWires_perm (setConstCircuit w c) _ (setConstCircuit_implements w c)
      (eqConstSetEmb w) z2 (fun j => Fin.elim0 j)
    rw [hact]; congr 1; funext u
    by_cases hu : u.1 < w
    · have hu_eq : u = ((Fin.castAddEmb 0).trans (eqConstSetEmb w)) ⟨u.1, hu⟩ := Fin.ext rfl
      rw [hu_eq, updateOn_apply_emb]
      have hne_t : u ≠ tgt := Fin.ne_of_val_ne (by dsimp [tgt]; omega)
      have hne_x : (⟨u.1, by omega⟩ : Fin (w + 1)) ≠ ⟨w, by omega⟩ := Fin.ne_of_val_ne (by simp; omega)
      dsimp only [Function.comp_apply]
      change xor (z2 u) (natToBitsLSB w c ⟨u.1, hu⟩) = _
      dsimp only [z2]; rw [← hu_eq, Function.update_of_ne hne_t]
      dsimp only [z1, z0]; rw [dif_pos hu, padZero_val_lt x u (by omega),
        padZero_val_lt _ u (by omega), eqConstFn, Function.update_of_ne hne_x]
      dsimp only [pat]
      cases x ⟨u.1, by omega⟩ <;> cases natToBitsLSB w c ⟨u.1, hu⟩ <;> simp
    · have hnot : u ∉ Set.range ((Fin.castAddEmb 0).trans (eqConstSetEmb w)) := by
        rintro ⟨j, hj⟩; have := congrArg Fin.val hj; simp at this; omega
      rw [updateOn_apply_not_mem _ _ _ hnot]
      by_cases huw : u = tgt
      · subst huw
        dsimp only [z2]; rw [Function.update_self, hz1_w]
        rw [padZero_val_lt _ tgt (by dsimp [tgt]; omega), eqConstFn, Function.update_self]
      · have hge : w + 1 ≤ u.1 := by
          have hne : u.1 ≠ w := fun h => huw (Fin.ext h)
          omega
        dsimp only [z2]; rw [Function.update_of_ne huw]
        dsimp only [z1, z0]; rw [dif_neg hu, padZero_val_ge x u hge, padZero_val_ge _ u hge]
  dsimp only [eqConstCircuit]
  simp only [LayeredCircuit.seq_unitary, act_mul]
  change act sc.unitary (act eqZ.unitary (act sc.unitary (ket z0))) = _
  rw [h1, h2, h3]


/-- In-place MSB-first particle encoding on `s` qubits (`s = Nat.clog 2 n + 1`). -/
private def ctrlMsbXorLowCircuit (s : ℕ) (hs : 1 ≤ s) (pat : Qubits (s - 1)) :
    (k : ℕ) → k ≤ s - 1 → LayeredCircuit s
  | 0, _ => LayeredCircuit.id s
  | k + 1, hk =>
    let prev := ctrlMsbXorLowCircuit s hs pat k (by omega)
    let tgt : Fin s := ⟨1 + k, by omega⟩
    have hne : (⟨0, hs⟩ : Fin s) ≠ tgt := Fin.ne_of_val_ne (by dsimp [tgt]; omega)
    if pat ⟨k, hk⟩ then prev.seq (cnotGate ⟨0, hs⟩ tgt hne) else prev

private lemma ctrlMsbXorLowCircuit_size (s : ℕ) (hs : 1 ≤ s) (pat : Qubits (s - 1))
    (k : ℕ) (hk : k ≤ s - 1) : (ctrlMsbXorLowCircuit s hs pat k hk).size ≤ k := by
  induction k with
  | zero => simp [ctrlMsbXorLowCircuit]
  | succ k ih =>
    dsimp only [ctrlMsbXorLowCircuit]
    split_ifs <;> have h := ih (by omega) <;> simp <;> omega

private lemma act_ctrlMsbXorLowCircuit_ket (s : ℕ) (hs : 1 ≤ s) (pat : Qubits (s - 1))
    (k : ℕ) (hk : k ≤ s - 1) (z : Qubits s) :
    act (ctrlMsbXorLowCircuit s hs pat k hk).unitary (ket z) =
      ket (fun u : Fin s =>
        if z ⟨0, hs⟩ then
          if h : 1 ≤ u.1 ∧ u.1 < 1 + k then xor (z u) (pat ⟨u.1 - 1, by omega⟩) else z u
        else z u) := by
  induction k with
  | zero =>
    simp only [ctrlMsbXorLowCircuit, LayeredCircuit.id_unitary, act_one]
    congr 1; funext u; cases z ⟨0, hs⟩
    · rfl
    · simp only [↓reduceIte]; rw [dif_neg (by omega)]
  | succ k ih =>
    dsimp only [ctrlMsbXorLowCircuit]
    cases hp : pat ⟨k, hk⟩
    · rw [if_neg (by simp), ih (by omega)]
      congr 1; funext u
      cases hz0 : z ⟨0, hs⟩
      · rfl
      · simp only [↓reduceIte]
        by_cases hu : 1 ≤ u.1 ∧ u.1 < 1 + k
        · rw [dif_pos hu, dif_pos (by omega)]
        · rw [dif_neg hu]
          by_cases heq : u.1 = 1 + k
          · have hidx : (⟨u.1 - 1, by have := u.isLt; omega⟩ : Fin (s - 1)) = ⟨k, hk⟩ :=
              Fin.ext (by dsimp; omega)
            rw [dif_pos (by omega), hidx, hp, Bool.xor_false]
          · rw [dif_neg (by omega)]
    · rw [if_pos (by simp), LayeredCircuit.seq_unitary, act_mul, ih (by omega),
        act_cnotGate_ket]
      congr 1; funext u
      let tgt : Fin s := ⟨1 + k, by omega⟩
      cases hz0 : z ⟨0, hs⟩
      · simp only [Bool.false_eq_true, ↓reduceIte, Bool.xor_false, Function.update_eq_self]
      · have h0_lt : ¬ (1 ≤ (⟨0, hs⟩ : Fin s).1 ∧ (⟨0, hs⟩ : Fin s).1 < 1 + k) := by simp
        simp only [↓reduceIte, dif_neg h0_lt]
        by_cases hut : u = tgt
        · subst hut
          have hnt : ¬ (1 ≤ tgt.1 ∧ tgt.1 < 1 + k) := by dsimp [tgt]; omega
          rw [Function.update_self, dif_neg hnt, dif_pos (by dsimp [tgt]; omega)]
          have hsub : (⟨tgt.1 - 1, by omega⟩ : Fin (s - 1)) = ⟨k, hk⟩ :=
            Fin.ext (by dsimp [tgt]; omega)
          rw [hsub, hp]
        · rw [Function.update_of_ne hut]
          by_cases hu : 1 ≤ u.1 ∧ u.1 < 1 + k
          · rw [dif_pos hu, dif_pos (by omega)]
          · rw [dif_neg hu, dif_neg (by intro h; apply hut; apply Fin.ext; dsimp [tgt]; omega)]

private def encSymEqEmb (s : ℕ) (hs : 1 ≤ s) : Fin ((s - 1) + 1 + (s - 1)) ↪ Fin (s + (s - 1)) where
  toFun i :=
    have hi := i.isLt
    if h1 : i.1 < s - 1 then ⟨1 + i.1, by omega⟩
    else if h2 : i.1 = s - 1 then ⟨0, by omega⟩
    else ⟨i.1, by omega⟩
  inj' a b h := by
    have hv := congrArg Fin.val h; dsimp only at hv
    split_ifs at hv <;> dsimp only at hv <;> exact Fin.ext (by omega)

@[simp] private lemma encSymEqEmb_val (s : ℕ) (hs : 1 ≤ s) (i : Fin ((s - 1) + 1 + (s - 1))) :
    (encSymEqEmb s hs i).1 =
      if i.1 < s - 1 then 1 + i.1 else if i.1 = s - 1 then 0 else i.1 := by
  change (if h1 : i.1 < s - 1 then (⟨1 + i.1, _⟩ : Fin (s + (s - 1)))
    else if h2 : i.1 = s - 1 then ⟨0, _⟩ else ⟨i.1, _⟩).1 = _
  split_ifs <;> rfl

private def encSymXorEmb (s : ℕ) : Fin s ↪ Fin (s + (s - 1)) := Fin.castAddEmb (s - 1)

noncomputable def encodeParticleSym54Circuit (n s : ℕ) (hs : s = Nat.clog 2 n + 1) :
    LayeredCircuit (s + (s - 1)) :=
  if hfull : n = 2 ^ (s - 1) then
    LayeredCircuit.id (s + (s - 1))
  else
    have hs1 : 1 ≤ s := by omega
    let low_n := natToBits (s - 1) n
    let step1 := (multiEqCtrl1 (s - 1) low_n pauliX pauliX_mem_unitaryGroup).mapWires
      (encSymEqEmb s hs1)
    let step2 := (ctrlMsbXorLowCircuit s hs1 low_n (s - 1) le_rfl).mapWires (encSymXorEmb s)
    step1.seq step2

lemma encodeParticleSym54Circuit_size (n s : ℕ) (hs : s = Nat.clog 2 n + 1) :
    (encodeParticleSym54Circuit n s hs).size ≤ 13 * s := by
  unfold encodeParticleSym54Circuit
  split_ifs with hfull
  · simp
  · simp only [LayeredCircuit.seq_size, LayeredCircuit.mapWires_size]
    have h1 := multiEqCtrl1_size (s - 1) (natToBits (s - 1) n) pauliX pauliX_mem_unitaryGroup
    have h2 := ctrlMsbXorLowCircuit_size s (by omega) (natToBits (s - 1) n) (s - 1) le_rfl
    omega

theorem encodeParticleSym54Circuit_act (n s : ℕ) (hn : 1 ≤ n) (hs : s = Nat.clog 2 n + 1)
    (j : Fin (n + 1)) :
    act (encodeParticleSym54Circuit n s hs).unitary (ket (padZero s (s - 1) (natToBits s j.1))) =
      ket (padZero s (s - 1) (particleSym54 n s j)) := by
  have _ := hn
  have hs1 : 1 ≤ s := by omega
  have hle_pow : n ≤ 2 ^ (s - 1) := by
    have := Nat.le_pow_clog (by norm_num : 1 < 2) n
    rw [hs]; simpa using this
  have hlt_pow : n < 2 ^ s := by
    have hpow : 2 ^ s = 2 * 2 ^ (s - 1) := by
      conv_lhs => rw [show s = (s - 1) + 1 by omega, pow_succ']
    have hpos : 0 < 2 ^ (s - 1) := Nat.two_pow_pos _
    omega
  have hj_lt : j.1 < 2 ^ s := lt_of_le_of_lt (Nat.le_of_lt_succ j.isLt) hlt_pow
  by_cases hfull : n = 2 ^ (s - 1)
  · simp only [encodeParticleSym54Circuit, dif_pos hfull, LayeredCircuit.id_unitary, act_one]
    congr 2
    dsimp [particleSym54]
    split_ifs with hj
    · rfl
    · have hj_last : j.1 = n := by have := j.isLt; omega
      rw [hj_last, hfull]; rfl
  · have hn_lt : n < 2 ^ (s - 1) := lt_of_le_of_ne hle_pow hfull
    simp only [encodeParticleSym54Circuit, dif_neg hfull, LayeredCircuit.seq_unitary, act_mul]
    let z0 := padZero s (s - 1) (natToBits s j.1)
    let tgt0 : Fin (s + (s - 1)) := ⟨0, by omega⟩
    let low_n := natToBits (s - 1) n
    let emb1 := encSymEqEmb s hs1
    let step1 := (multiEqCtrl1 (s - 1) low_n pauliX pauliX_mem_unitaryGroup).mapWires emb1
    let step2 := (ctrlMsbXorLowCircuit s hs1 low_n (s - 1) le_rfl).mapWires (encSymXorEmb s)
    have hnat_msb : ∀ x : ℕ, x < 2 ^ (s - 1) → natToBits s x ⟨0, hs1⟩ = false := by
      intro x hx
      rw [natToBits_apply (lt_trans hx (Nat.pow_lt_pow_right (by norm_num) (by omega)))]
      simp only [natToBitsLSB, Fin.val_rev, show s - (0 + 1) = s - 1 by omega]
      exact Nat.testBit_lt_two_pow hx
    have hnat_low : ∀ x : ℕ, x < 2 ^ (s - 1) → ∀ k : Fin (s - 1),
        natToBits s x ⟨1 + k.1, by omega⟩ = natToBits (s - 1) x k := by
      intro x hx k
      have hlt_s : x < 2 ^ s := lt_trans hx (Nat.pow_lt_pow_right (by norm_num) (by omega))
      rw [natToBits_apply hlt_s, natToBits_apply hx]
      simp only [natToBitsLSB, Fin.val_rev]
      congr 1; omega
    have hlow_inj : ∀ x y : ℕ, x < 2 ^ (s - 1) → y < 2 ^ (s - 1) →
        natToBits (s - 1) x = natToBits (s - 1) y → x = y := by
      intro x y hx hy heq
      have h1 := congrArg bitsToNat heq
      have hb : ∀ u, u < 2 ^ (s - 1) → bitsToNat (natToBits (s - 1) u) = u := fun u hu => by
        rw [← bitsEquivFin_apply]; simp [natToBits, Nat.mod_eq_of_lt hu]
      rwa [hb x hx, hb y hy] at h1
    have hclean_z0 : ∀ r : Fin (s - 1), z0 (emb1 (Fin.natAdd ((s - 1) + 1) r)) = false := fun r => by
      have hr : ¬ ((s - 1 + 1 + r.1) < s - 1) := by omega
      have hne : (s - 1 + 1 + r.1) ≠ s - 1 := by omega
      have hev : (emb1 (Fin.natAdd ((s - 1) + 1) r)).1 = s - 1 + 1 + r.1 := by
        simp [emb1, hr, hne]
      dsimp only [z0]; exact padZero_val_ge _ _ (by omega)
    let z1 := Function.update z0 tgt0 (decide (j.1 = n))
    have hstep1 : act step1.unitary (ket z0) = ket z1 := by
      have hact := act_mapWires_perm (multiEqCtrl1 (s - 1) low_n pauliX pauliX_mem_unitaryGroup) _
        (multiEqCtrl1_implements_perm (s - 1) low_n) emb1 z0 hclean_z0
      rw [hact]; congr 1; funext u
      let embM := (Fin.castAddEmb (s - 1)).trans emb1
      have htgt : tgt0 = embM ⟨s - 1, Nat.lt_succ_self (s - 1)⟩ := by
        apply Fin.ext; simp [tgt0, embM, emb1]
      have hlow_eq : (∀ i : Fin (s - 1), z0 (embM ⟨i.1, by omega⟩) = low_n i) ↔ j.1 = n := by
        have hj_pow : j.1 < 2 ^ (s - 1) := lt_of_le_of_lt (Nat.le_of_lt_succ j.isLt) hn_lt
        have heq_f : (fun i : Fin (s - 1) => z0 (embM ⟨i.1, by omega⟩)) = natToBits (s - 1) j.1 := by
          funext i
          have hev : (embM ⟨i.1, by omega⟩).1 = 1 + i.1 := by simp [embM, emb1, i.isLt]
          dsimp only [z0]
          rw [padZero_val_lt _ _ (by omega)]
          have h1eq : (⟨(embM ⟨i.1, by omega⟩).1, by omega⟩ : Fin s) =
              ⟨1 + i.1, by omega⟩ := Fin.ext hev
          rw [h1eq, hnat_low j.1 hj_pow i]
        constructor
        · intro h
          have heq_b : natToBits (s - 1) j.1 = natToBits (s - 1) n := by
            funext i; rw [← heq_f]; exact h i
          exact hlow_inj j.1 n hj_pow hn_lt heq_b
        · intro hjn i
          rw [congrFun heq_f i, hjn]
      have hdec : decide (∀ i : Fin (s - 1), (z0 ∘ embM) ⟨i.1, by omega⟩ = low_n i) =
          decide (j.1 = n) := by
        rw [Bool.eq_iff_iff]; simp only [Function.comp_apply, decide_eq_true_eq]; exact hlow_eq
      by_cases hu : u = tgt0
      · subst hu
        dsimp only [embM] at htgt
        rw [htgt, updateOn_apply_emb, Function.update_self]
        dsimp only [z1]; rw [← htgt, Function.update_self]
        simp only [Function.comp_apply] at hdec ⊢
        have hj_pow : j.1 < 2 ^ (s - 1) := lt_of_le_of_lt (Nat.le_of_lt_succ j.isLt) hn_lt
        have hz_0 : z0 tgt0 = false := by
          dsimp only [z0]
          rw [padZero_val_lt _ _ (by dsimp [tgt0]; omega)]
          exact hnat_msb j.1 hj_pow
        rw [← htgt, hz_0, Bool.false_xor, hdec]
      · dsimp only [z1]; rw [Function.update_of_ne hu]
        by_cases hur : u ∈ Set.range embM
        · rcases hur with ⟨k, rfl⟩
          rw [updateOn_apply_emb]
          rcases Fin.eq_castSucc_or_eq_last k with ⟨k', rfl⟩ | rfl
          · have hne : k'.castSucc ≠ ⟨s - 1, Nat.lt_succ_self (s - 1)⟩ := Fin.ne_of_val_ne (by simp; omega)
            rw [Function.update_of_ne hne]; rfl
          · exfalso; exact hu htgt.symm
        · rw [updateOn_apply_not_mem _ _ _ hur]
    have hstep2 : act step2.unitary (ket z1) = ket (padZero s (s - 1) (particleSym54 n s j)) := by
      have hact := act_mapWires_ket (ctrlMsbXorLowCircuit s hs1 low_n (s - 1) le_rfl)
        (encSymXorEmb s) z1 _ (act_ctrlMsbXorLowCircuit_ket s hs1 low_n (s - 1) le_rfl (z1 ∘ encSymXorEmb s))
        (padZero s (s - 1) (particleSym54 n s j)) ?_ ?_
      · exact hact
      · funext u
        dsimp only [Function.comp_apply]
        have henc : encSymXorEmb s u = Fin.castAdd (s - 1) u := rfl
        rw [henc, padZero_castAdd]
        have hj_pow : j.1 < 2 ^ (s - 1) := lt_of_le_of_lt (Nat.le_of_lt_succ j.isLt) hn_lt
        have hz1_0 : z1 (encSymXorEmb s ⟨0, hs1⟩) = decide (j.1 = n) := by
          have : encSymXorEmb s ⟨0, hs1⟩ = tgt0 := Fin.ext rfl
          rw [this]; dsimp only [z1]; rw [Function.update_self]
        by_cases hjn : j.1 = n
        · have hj_last : j = Fin.last n := Fin.ext hjn
          have hz1_t : z1 (encSymXorEmb s ⟨0, hs1⟩) = true := by
            rw [hz1_0, decide_eq_true hjn]
          have hz1_tc : z1 (Fin.castAdd (s - 1) ⟨0, hs1⟩) = true := hz1_t
          simp only [hj_last, particleSym54_last, blankSym54, hz1_t, ↓reduceIte]
          by_cases hu0 : u.1 = 0
          · have : u = ⟨0, hs1⟩ := Fin.ext hu0
            subst this
            rw [dif_neg (by omega), hz1_tc]
            have h2pow : 2 ^ (s - 1) < 2 ^ s := Nat.pow_lt_pow_right (by norm_num) (by omega)
            rw [natToBits_apply h2pow]
            simp [natToBitsLSB]
          · have h1u : 1 ≤ u.1 ∧ u.1 < 1 + (s - 1) := by have := u.isLt; omega
            rw [dif_pos h1u]
            have hne0 : Fin.castAdd (s - 1) u ≠ tgt0 := Fin.ne_of_val_ne (by simp [tgt0, hu0])
            dsimp only [z1, z0]; rw [Function.update_of_ne hne0, padZero_val_lt _ _ (by simp)]
            have hlow_n : natToBits s n ⟨u.1, u.isLt⟩ = low_n ⟨u.1 - 1, by omega⟩ := by
              have hu_eq : (⟨u.1, u.isLt⟩ : Fin s) = ⟨1 + (u.1 - 1), by omega⟩ :=
                Fin.ext (by dsimp; omega)
              conv_lhs => rw [hu_eq]
              exact hnat_low n hn_lt ⟨u.1 - 1, by omega⟩
            have hxu : natToBits s j.1 ⟨u.1, u.isLt⟩ = low_n ⟨u.1 - 1, by omega⟩ := by
              rw [hjn]; exact hlow_n
            have hcast_u : (⟨(Fin.castAdd (s - 1) u).1, by simp⟩ : Fin s) = ⟨u.1, u.isLt⟩ :=
              Fin.ext (by simp)
            rw [hcast_u, hxu, Bool.xor_self]
            have h2pow : 2 ^ (s - 1) < 2 ^ s := Nat.pow_lt_pow_right (by norm_num) (by omega)
            rw [natToBits_apply h2pow]
            simp only [natToBitsLSB, Fin.val_rev, Nat.testBit_two_pow]
            exact decide_eq_false (by omega)
        · have hjn_lt : j.1 < n := by have := j.isLt; omega
          have hz1_f : z1 (encSymXorEmb s ⟨0, hs1⟩) = false := by rw [hz1_0]; exact decide_eq_false hjn
          have hz1_fc : z1 (Fin.castAdd (s - 1) ⟨0, hs1⟩) = false := hz1_f
          simp only [hz1_f, Bool.false_eq_true, ↓reduceIte, particleSym54_lt hjn_lt]
          by_cases hu0 : u.1 = 0
          · have : u = ⟨0, hs1⟩ := Fin.ext hu0
            subst this
            rw [hz1_fc, hnat_msb j.1 hj_pow]
          · have hne0 : Fin.castAdd (s - 1) u ≠ tgt0 := Fin.ne_of_val_ne (by simp [tgt0, hu0])
            dsimp only [z1, z0]; rw [Function.update_of_ne hne0, padZero_val_lt _ _ (by simp)]
            rfl
      · intro w hw
        have hw_ge : s ≤ w.1 := by
          by_contra hlt; exact hw ⟨⟨w.1, by omega⟩, Fin.ext rfl⟩
        have hne0 : w ≠ tgt0 := Fin.ne_of_val_ne (by dsimp [tgt0]; omega)
        dsimp only [z1, z0]; rw [Function.update_of_ne hne0]
        rw [padZero_val_ge _ w hw_ge, padZero_val_ge _ w hw_ge]
    change act step2.unitary (act step1.unitary (ket z0)) = _
    rw [hstep1, hstep2]

/-! ### Part 4: Recursive Cuccaro In-Place Adder & Unsigned Comparator -/

private noncomputable def cuccaroMAJ {m : ℕ} (c b a : Fin m)
    (hcb : c ≠ b) (hca : c ≠ a) (hba : b ≠ a) : LayeredCircuit m :=
  (cnotGate a b hba.symm).seq ((cnotGate a c hca.symm).seq (toffoliOn c b a hcb hca hba))

private noncomputable def cuccaroUMA {m : ℕ} (c b a : Fin m)
    (hcb : c ≠ b) (hca : c ≠ a) (hba : b ≠ a) : LayeredCircuit m :=
  (toffoliOn c b a hcb hca hba).seq ((cnotGate a c hca.symm).seq (cnotGate c b hcb))

@[simp] private lemma cuccaroMAJ_size {m : ℕ} (c b a : Fin m)
    (hcb : c ≠ b) (hca : c ≠ a) (hba : b ≠ a) : (cuccaroMAJ c b a hcb hca hba).size = 7 := by
  simp [cuccaroMAJ]

@[simp] private lemma cuccaroUMA_size {m : ℕ} (c b a : Fin m)
    (hcb : c ≠ b) (hca : c ≠ a) (hba : b ≠ a) : (cuccaroUMA c b a hcb hca hba).size = 7 := by
  simp [cuccaroUMA]

private lemma act_cuccaroMAJ_ket {m : ℕ} (c b a : Fin m)
    (hcb : c ≠ b) (hca : c ≠ a) (hba : b ≠ a) (z : Qubits m) :
    act (cuccaroMAJ c b a hcb hca hba).unitary (ket z) =
      ket (fun w =>
        if w = c then xor (z c) (z a)
        else if w = b then xor (z b) (z a)
        else if w = a then xor (z a) ((xor (z c) (z a)) && (xor (z b) (z a)))
        else z w) := by
  simp only [cuccaroMAJ, LayeredCircuit.seq_unitary, act_mul, act_cnotGate_ket, act_toffoliOn_ket]
  congr 1; funext w
  by_cases hwc : w = c
  · subst hwc
    simp only [Function.update_self, Function.update_of_ne hca, Function.update_of_ne hcb,
      Function.update_of_ne hca.symm, Function.update_of_ne hcb.symm,
      Function.update_of_ne hba.symm, ↓reduceIte]
  · by_cases hwb : w = b
    · subst hwb
      simp only [Function.update_self, Function.update_of_ne hba, Function.update_of_ne hba.symm,
        Function.update_of_ne hcb, Function.update_of_ne hcb.symm,
        Function.update_of_ne hca.symm, if_neg hwc, ↓reduceIte]
    · by_cases hwa : w = a
      · subst hwa
        simp only [Function.update_self, Function.update_of_ne hca.symm,
          Function.update_of_ne hba.symm,
          Function.update_of_ne hcb, Function.update_of_ne hcb.symm,
          if_neg hwc, if_neg hwb, ↓reduceIte]
      · rw [Function.update_of_ne hwa, Function.update_of_ne hwc, Function.update_of_ne hwb,
          if_neg hwc, if_neg hwb, if_neg hwa]

private lemma act_cuccaroUMA_ket {m : ℕ} (c b a : Fin m)
    (hcb : c ≠ b) (hca : c ≠ a) (hba : b ≠ a) (z : Qubits m) :
    act (cuccaroUMA c b a hcb hca hba).unitary (ket z) =
      ket (fun w =>
        let a1 := xor (z a) (z c && z b)
        let c1 := xor (z c) a1
        if w = c then c1
        else if w = b then xor (z b) c1
        else if w = a then a1
        else z w) := by
  simp only [cuccaroUMA, LayeredCircuit.seq_unitary, act_mul, act_cnotGate_ket, act_toffoliOn_ket]
  congr 1; funext w
  by_cases hwc : w = c
  · subst hwc
    simp only [Function.update_self, Function.update_of_ne hcb, Function.update_of_ne hcb.symm,
      Function.update_of_ne hca, Function.update_of_ne hba, ↓reduceIte]
  · by_cases hwb : w = b
    · subst hwb
      simp only [Function.update_self, Function.update_of_ne hba,
        Function.update_of_ne hcb.symm,
        Function.update_of_ne hca, if_neg hwc, ↓reduceIte]
    · by_cases hwa : w = a
      · subst hwa
        simp only [Function.update_self, Function.update_of_ne hwc, Function.update_of_ne hwb,
          Function.update_of_ne hca,
          Function.update_of_ne hba,
          Function.update_of_ne hcb.symm,
          if_neg hwc, if_neg hwb, ↓reduceIte]
      · rw [Function.update_of_ne hwb, Function.update_of_ne hwc, Function.update_of_ne hwa,
          if_neg hwc, if_neg hwb, if_neg hwa]

private lemma bool_maj_carry (va vb vc : Bool) :
    xor va ((xor vc va) && (xor vb va)) =
      decide (2 ≤ (if va then 1 else 0) + (if vb then 1 else 0) + (if vc then 1 else 0)) := by
  cases va <;> cases vb <;> cases vc <;> decide

private lemma bool_uma_step (va vb vc : Bool) :
    let c1 := xor vc va
    let b1 := xor vb va
    let a1 := xor va (c1 && b1)
    let a2 := xor a1 (c1 && b1)
    let c2 := xor c1 a2
    let b2 := xor b1 c2
    a2 = va ∧ c2 = vc ∧ b2 = xor (xor va vb) vc := by
  cases va <;> cases vb <;> cases vc <;> decide

/-- Shift embedding `Fin (1 + 2 * w) ↪ Fin (1 + 2 * (w + 1))` mapping `0 ↦ 1` (`a_0`) and `1+j ↦ 3+j`. -/
private def cuccaroShiftEmb (w : ℕ) : Fin (1 + 2 * w) ↪ Fin (1 + 2 * (w + 1)) where
  toFun i := if i.1 = 0 then ⟨1, by omega⟩ else ⟨i.1 + 2, by have := i.isLt; omega⟩
  inj' a b h := by
    have hv := congrArg Fin.val h; dsimp only at hv
    by_cases ha : a.1 = 0 <;> by_cases hb : b.1 = 0
    · exact Fin.ext (ha.trans hb.symm)
    · simp only [ha, hb, ↓reduceIte] at hv; omega
    · simp only [ha, hb, ↓reduceIte] at hv; omega
    · simp only [ha, hb, ↓reduceIte] at hv; exact Fin.ext (by omega)

@[simp] private lemma cuccaroShiftEmb_val (w : ℕ) (i : Fin (1 + 2 * w)) :
    (cuccaroShiftEmb w i).1 = if i.1 = 0 then 1 else i.1 + 2 := by
  change (if i.1 = 0 then (⟨1, _⟩ : Fin (1 + 2 * (w + 1))) else ⟨i.1 + 2, _⟩).1 = _
  split_ifs <;> rfl

/-- Recursive Cuccaro core on interleaved wires `(c0, a_0, b_0, ..., a_{w-1}, b_{w-1})`. -/
noncomputable def cuccaroCore : (w : ℕ) → LayeredCircuit (1 + 2 * w)
  | 0 => LayeredCircuit.id 1
  | w + 1 =>
    let maj0 := cuccaroMAJ (⟨0, by omega⟩ : Fin (1 + 2 * (w + 1))) ⟨2, by omega⟩ ⟨1, by omega⟩
      (Fin.ne_of_val_ne (by simp)) (Fin.ne_of_val_ne (by simp)) (Fin.ne_of_val_ne (by simp))
    let mid := (cuccaroCore w).mapWires (cuccaroShiftEmb w)
    let uma0 := cuccaroUMA (⟨0, by omega⟩ : Fin (1 + 2 * (w + 1))) ⟨2, by omega⟩ ⟨1, by omega⟩
      (Fin.ne_of_val_ne (by simp)) (Fin.ne_of_val_ne (by simp)) (Fin.ne_of_val_ne (by simp))
    maj0.seq (mid.seq uma0)

lemma cuccaroCore_size (w : ℕ) : (cuccaroCore w).size = 14 * w := by
  induction w with
  | zero => simp [cuccaroCore]
  | succ w ih =>
    simp only [cuccaroCore, LayeredCircuit.seq_size, LayeredCircuit.mapWires_size,
      cuccaroMAJ_size, cuccaroUMA_size, ih]
    omega

theorem act_cuccaroCore_ket (w : ℕ) (cin : Bool) (a b : Qubits w) :
    let init : Qubits (1 + 2 * w) := fun u =>
      if h0 : u.1 = 0 then cin
      else if hm : (u.1 - 1) % 2 = 0 then a ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩
      else b ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩
    let sNat := bitsToNatLSB a + bitsToNatLSB b + (if cin then 1 else 0)
    let sout := natToBitsLSB w sNat
    let out : Qubits (1 + 2 * w) := fun u =>
      if h0 : u.1 = 0 then cin
      else if hm : (u.1 - 1) % 2 = 0 then a ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩
      else sout ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩
    act (cuccaroCore w).unitary (ket init) = ket out := by
  induction w generalizing cin with
  | zero =>
    intro init sNat sout out
    simp only [cuccaroCore, LayeredCircuit.id_unitary, act_one]
    congr 1; funext u
    simp [init, out]
  | succ w ih =>
    intro init sNat sout out
    dsimp only [cuccaroCore]
    simp only [LayeredCircuit.seq_unitary, act_mul]
    let c0 : Fin (1 + 2 * (w + 1)) := ⟨0, by omega⟩
    let a0 : Fin (1 + 2 * (w + 1)) := ⟨1, by omega⟩
    let b0 : Fin (1 + 2 * (w + 1)) := ⟨2, by omega⟩
    have hc0_v : c0.1 = 0 := rfl
    have ha0_v : a0.1 = 1 := rfl
    have hb0_v : b0.1 = 2 := rfl
    have hc_init : init c0 = cin := by dsimp [init, c0]
    have ha_init : init a0 = a 0 := by
      dsimp only [init]; rw [dif_neg (by omega), dif_pos (by omega)]
      exact congrArg a (Fin.ext (by dsimp; omega))
    have hb_init : init b0 = b 0 := by
      dsimp only [init]; rw [dif_neg (by omega), dif_neg (by omega)]
      exact congrArg b (Fin.ext (by dsimp; omega))
    let a' : Qubits w := fun i => a i.succ
    let b' : Qubits w := fun i => b i.succ
    let cin' := decide (2 ≤ (if a 0 then 1 else 0) + (if b 0 then 1 else 0) + (if cin then 1 else 0))
    let z1 : Qubits (1 + 2 * (w + 1)) := fun u =>
      if u = c0 then xor cin (a 0)
      else if u = b0 then xor (b 0) (a 0)
      else if u = a0 then cin'
      else init u
    have hmaj : act (cuccaroMAJ c0 b0 a0 (Fin.ne_of_val_ne (by omega))
        (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))).unitary (ket init) =
        ket z1 := by
      rw [act_cuccaroMAJ_ket]
      congr 1; funext u
      rw [hc_init, ha_init, hb_init]
      by_cases huc : u = c0
      · simp [z1, huc]
      · by_cases hub : u = b0
        · simp [z1, hub]
        · by_cases hua : u = a0
          · simp [z1, hua, cin', bool_maj_carry]
          · simp [z1, huc, hub, hua]
    have hih := ih cin' a' b'
    dsimp only at hih
    let emb := cuccaroShiftEmb w
    have hz1_comp : z1 ∘ emb = fun u : Fin (1 + 2 * w) =>
        if h0 : u.1 = 0 then cin'
        else if hm : (u.1 - 1) % 2 = 0 then a' ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩
        else b' ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩ := by
      funext u
      dsimp only [Function.comp_apply]
      by_cases hu0 : u.1 = 0
      · have he : emb u = a0 := Fin.ext (by simp [emb, a0, hu0])
        rw [he, dif_pos hu0]
        dsimp only [z1]
        have h1 : a0 ≠ c0 := Fin.ne_of_val_ne (by omega)
        have h2 : a0 ≠ b0 := Fin.ne_of_val_ne (by omega)
        rw [if_neg h1, if_neg h2, if_pos rfl]
      · rw [dif_neg hu0]
        have hev : (emb u).1 = u.1 + 2 := by simp [emb, hu0]
        have hnc : emb u ≠ c0 := Fin.ne_of_val_ne (by omega)
        have hnb : emb u ≠ b0 := Fin.ne_of_val_ne (by omega)
        have hna : emb u ≠ a0 := Fin.ne_of_val_ne (by omega)
        dsimp only [z1]; rw [if_neg hnc, if_neg hnb, if_neg hna]
        dsimp only [init, a', b']
        rw [dif_neg (by omega)]
        have hmod : ((emb u).1 - 1) % 2 = 0 ↔ (u.1 - 1) % 2 = 0 := by omega
        have hdiv : ((emb u).1 - 1) / 2 = (u.1 - 1) / 2 + 1 := by omega
        by_cases hp1 : ((emb u).1 - 1) % 2 = 0 <;> by_cases hp2 : (u.1 - 1) % 2 = 0
        · rw [dif_pos hp1, dif_pos hp2]; exact congrArg a (Fin.ext (by dsimp [Fin.succ]; omega))
        · exact absurd (hmod.mp hp1) hp2
        · exact absurd (hmod.mpr hp2) hp1
        · rw [dif_neg hp1, dif_neg hp2]; exact congrArg b (Fin.ext (by dsimp [Fin.succ]; omega))
    let sNat' := bitsToNatLSB a' + bitsToNatLSB b' + (if cin' then 1 else 0)
    let sout' := natToBitsLSB w sNat'
    let z2 : Qubits (1 + 2 * (w + 1)) := fun u =>
      if hc : u = c0 then xor cin (a 0)
      else if hb : u = b0 then xor (b 0) (a 0)
      else if ha : u = a0 then cin'
      else if hm : (u.1 - 1) % 2 = 0 then a ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩
      else sout' ⟨(u.1 - 1) / 2 - 1, by
        have hu3 : 3 ≤ u.1 := by
          by_contra hlt
          have : u.1 = 0 ∨ u.1 = 1 ∨ u.1 = 2 := by omega
          rcases this with h | h | h
          · exact hc (Fin.ext h)
          · exact ha (Fin.ext h)
          · exact hb (Fin.ext h)
        have := u.isLt; omega⟩
    have hmid : act ((cuccaroCore w).mapWires emb).unitary (ket z1) = ket z2 := by
      refine act_mapWires_ket (cuccaroCore w) emb z1 _ (by rw [hz1_comp]; exact hih) z2 ?_ ?_
      · funext u
        dsimp only [Function.comp_apply]
        by_cases hu0 : u.1 = 0
        · have he : emb u = a0 := Fin.ext (by simp [emb, a0, hu0])
          rw [he, dif_pos hu0]
          dsimp only [z2]
          rw [dif_neg (Fin.ne_of_val_ne (by omega)),
            dif_neg (Fin.ne_of_val_ne (by omega)), dif_pos rfl]
        · rw [dif_neg hu0]
          have hev : (emb u).1 = u.1 + 2 := by simp [emb, hu0]
          have hnc : emb u ≠ c0 := Fin.ne_of_val_ne (by omega)
          have hnb : emb u ≠ b0 := Fin.ne_of_val_ne (by omega)
          have hna : emb u ≠ a0 := Fin.ne_of_val_ne (by omega)
          dsimp only [z2]; rw [dif_neg hnc, dif_neg hnb, dif_neg hna]
          have hmod : ((emb u).1 - 1) % 2 = 0 ↔ (u.1 - 1) % 2 = 0 := by omega
          have hdiv1 : ((emb u).1 - 1) / 2 = (u.1 - 1) / 2 + 1 := by omega
          have hdiv2 : ((emb u).1 - 1) / 2 - 1 = (u.1 - 1) / 2 := by omega
          by_cases hp1 : ((emb u).1 - 1) % 2 = 0 <;> by_cases hp2 : (u.1 - 1) % 2 = 0
          · rw [dif_pos hp1, dif_pos hp2]; exact congrArg a (Fin.ext (by dsimp [Fin.succ]; omega))
          · exact absurd (hmod.mp hp1) hp2
          · exact absurd (hmod.mpr hp2) hp1
          · rw [dif_neg hp1, dif_neg hp2]; exact congrArg sout' (Fin.ext (by dsimp; omega))
      · intro u hu
        have hu_le2 : u.1 = 0 ∨ u.1 = 2 := by
          by_contra h
          have hne0 : u.1 ≠ 0 := fun h0 => h (Or.inl h0)
          have hne2 : u.1 ≠ 2 := fun h2 => h (Or.inr h2)
          by_cases hu1 : u.1 = 1
          · exact hu ⟨0, Fin.ext (by simp [emb, hu1])⟩
          · exact hu ⟨⟨u.1 - 2, by have := u.isLt; omega⟩,
              Fin.ext (by simp [emb, show u.1 - 2 ≠ 0 by omega]; omega)⟩
        rcases hu_le2 with h0 | h2
        · have huc : u = c0 := Fin.ext h0
          rw [huc]; simp [z1, z2]
        · have hub : u = b0 := Fin.ext h2
          rw [hub]; simp [z1, z2]
    have hsNat_eq : sNat = 2 * sNat' + (if xor (xor (a 0) (b 0)) cin then 1 else 0) := by
      have ha_s : bitsToNatLSB a = 2 * bitsToNatLSB a' + (if a 0 then 1 else 0) := by
        simp only [bitsToNatLSB, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, pow_zero]
        have hs : (∑ i : Fin w, if a i.succ then 2 ^ (i.1 + 1) else 0) =
            2 * ∑ i : Fin w, if a' i then 2 ^ i.1 else 0 := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
          dsimp [a']; split_ifs <;> simp [pow_succ']
        rw [hs]; omega
      have hb_s : bitsToNatLSB b = 2 * bitsToNatLSB b' + (if b 0 then 1 else 0) := by
        simp only [bitsToNatLSB, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, pow_zero]
        have hs : (∑ i : Fin w, if b i.succ then 2 ^ (i.1 + 1) else 0) =
            2 * ∑ i : Fin w, if b' i then 2 ^ i.1 else 0 := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
          dsimp [b']; split_ifs <;> simp [pow_succ']
        rw [hs]; omega
      dsimp only [sNat, sNat']
      rw [ha_s, hb_s]
      cases hax : a 0 <;> cases hbx : b 0 <;> cases hcx : cin <;> simp [cin', hax, hbx, hcx] <;> omega
    have hsout0 : sout 0 = xor (xor (a 0) (b 0)) cin := by
      simp only [sout, natToBitsLSB, Fin.val_zero, Nat.testBit_zero]
      rw [hsNat_eq]
      cases xor (xor (a 0) (b 0)) cin <;> simp
    have hsout_succ : ∀ i : Fin w, sout i.succ = sout' i := fun i => by
      simp only [sout, sout', natToBitsLSB, Fin.val_succ]
      rw [hsNat_eq, Nat.testBit_succ]
      have hdiv2 : (2 * sNat' + (if xor (xor (a 0) (b 0)) cin then 1 else 0)) / 2 = sNat' := by
        split_ifs <;> omega
      rw [hdiv2]
    rw [hmaj, hmid, act_cuccaroUMA_ket]
    congr 1; funext u
    have hbc : b0 ≠ c0 := Fin.ne_of_val_ne (by omega)
    have hac : a0 ≠ c0 := Fin.ne_of_val_ne (by omega)
    have hab : a0 ≠ b0 := Fin.ne_of_val_ne (by omega)
    have hz2_c : z2 c0 = xor cin (a 0) := by simp [z2]
    have hz2_b : z2 b0 = xor (b 0) (a 0) := by simp [z2, hbc]
    have hz2_a : z2 a0 = cin' := by simp [z2, hac, hab]
    have hcin' : cin' = xor (a 0) (xor cin (a 0) && xor (b 0) (a 0)) := (bool_maj_carry (a 0) (b 0) cin).symm
    have huma_a : xor (z2 a0) (z2 c0 && z2 b0) = a 0 := by
      rw [hz2_a, hz2_c, hz2_b, hcin']
      cases a 0 <;> cases b 0 <;> cases cin <;> rfl
    have huma_c : xor (z2 c0) (xor (z2 a0) (z2 c0 && z2 b0)) = cin := by
      rw [hz2_a, hz2_c, hz2_b, hcin']
      cases a 0 <;> cases b 0 <;> cases cin <;> rfl
    have huma_b : xor (z2 b0) (xor (z2 c0) (xor (z2 a0) (z2 c0 && z2 b0))) =
        xor (xor (a 0) (b 0)) cin := by
      rw [hz2_a, hz2_c, hz2_b, hcin']
      cases a 0 <;> cases b 0 <;> cases cin <;> rfl
    by_cases huc : u = c0
    · subst huc; rw [if_pos rfl, huma_c]; dsimp [out, c0]
    · rw [if_neg huc]
      by_cases hub : u = b0
      · subst hub; rw [if_pos rfl, huma_b]
        dsimp only [out]; rw [dif_neg (by omega), dif_neg (by omega)]
        have hb0_idx : (⟨(b0.1 - 1) / 2, by have := b0.isLt; omega⟩ : Fin (w + 1)) = 0 :=
          Fin.ext (by dsimp; omega)
        rw [hb0_idx, hsout0]
      · rw [if_neg hub]
        by_cases hua : u = a0
        · subst hua; rw [if_pos rfl, huma_a]
          dsimp only [out]; rw [dif_neg (by omega), dif_pos (by omega)]
          exact congrArg a (Fin.ext (by dsimp; omega))
        · rw [if_neg hua]
          have hge3 : 3 ≤ u.1 := by
            by_contra h; have h1 : u.1 = 0 ∨ u.1 = 1 ∨ u.1 = 2 := by omega
            rcases h1 with h | h | h
            · exact huc (Fin.ext h)
            · exact hua (Fin.ext h)
            · exact hub (Fin.ext h)
          have hu0 : u.1 ≠ 0 := by omega
          dsimp only [z2, out]
          rw [dif_neg huc, dif_neg hub, dif_neg hua, dif_neg hu0]
          by_cases hm : (u.1 - 1) % 2 = 0
          · rw [dif_pos hm, dif_pos hm]
          · rw [dif_neg hm, dif_neg hm]
            have hidx_eq : (⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩ : Fin (w + 1)) =
                Fin.succ ⟨(u.1 - 1) / 2 - 1, by have := u.isLt; omega⟩ := by
              apply Fin.ext; dsimp [Fin.succ]; omega
            rw [hidx_eq, hsout_succ]

private def cuccaroWireEmb (w : ℕ) : Fin (1 + 2 * w) ↪ Fin ((w + w) + 1) where
  toFun u :=
    if u.1 = 0 then ⟨w + w, by omega⟩
    else if (u.1 - 1) % 2 = 0 then ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩
    else ⟨w + (u.1 - 1) / 2, by have := u.isLt; omega⟩
  inj' a b h := by
    have ha := a.isLt; have hb := b.isLt
    have hv := congrArg Fin.val h; dsimp only at hv
    split_ifs at hv <;> dsimp only at hv <;> exact Fin.ext (by omega)

@[simp] private lemma cuccaroWireEmb_val (w : ℕ) (u : Fin (1 + 2 * w)) :
    (cuccaroWireEmb w u).1 =
      if u.1 = 0 then w + w
      else if (u.1 - 1) % 2 = 0 then (u.1 - 1) / 2
      else w + (u.1 - 1) / 2 := by
  change (if u.1 = 0 then (⟨w + w, _⟩ : Fin ((w + w) + 1))
    else if (u.1 - 1) % 2 = 0 then ⟨(u.1 - 1) / 2, _⟩ else ⟨w + (u.1 - 1) / 2, _⟩).1 = _
  split_ifs <;> rfl

/-- In-place `w`-bit adder `(a, b) ↦ (a, natToBitsLSB w (bitsToNatLSB a + bitsToNatLSB b))`
in `14 * w` gates with `1` clean ancilla. -/
noncomputable def addInPlaceCircuit (w : ℕ) : LayeredCircuit ((w + w) + 1) :=
  (cuccaroCore w).mapWires (cuccaroWireEmb w)

lemma addInPlaceCircuit_size (w : ℕ) : (addInPlaceCircuit w).size = 14 * w := by
  simp [addInPlaceCircuit, cuccaroCore_size]

def addInPlaceFn (w : ℕ) (x : Qubits (w + w)) : Qubits (w + w) :=
  let a : Qubits w := fun i => x ⟨i.1, by omega⟩
  let b : Qubits w := fun i => x ⟨w + i.1, by omega⟩
  let sum := natToBitsLSB w (bitsToNatLSB a + bitsToNatLSB b)
  fun i => if h : i.1 < w then a ⟨i.1, h⟩ else sum ⟨i.1 - w, by omega⟩

theorem addInPlaceCircuit_implements (w : ℕ) :
    (addInPlaceCircuit w).ImplementsOnClean (permMat (addInPlaceFn w)) := by
  apply implementsOnClean_of_act_perm
  intro x
  let z0 := padZero (w + w) 1 x
  let a : Qubits w := fun i => x ⟨i.1, by omega⟩
  let b : Qubits w := fun i => x ⟨w + i.1, by omega⟩
  let emb := cuccaroWireEmb w
  have hz0_comp : z0 ∘ emb = fun u : Fin (1 + 2 * w) =>
      if h0 : u.1 = 0 then false
      else if hm : (u.1 - 1) % 2 = 0 then a ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩
      else b ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩ := by
    funext u
    dsimp only [Function.comp_apply]
    by_cases h0 : u.1 = 0
    · rw [dif_pos h0]; dsimp only [z0]; exact padZero_val_ge x _ (by simp [emb, h0])
    · rw [dif_neg h0]
      by_cases hm : (u.1 - 1) % 2 = 0
      · have hev : (emb u).1 = (u.1 - 1) / 2 := by simp [emb, h0, hm]
        have hu_lt : (u.1 - 1) / 2 < w := by have := u.isLt; omega
        rw [dif_pos hm]; dsimp only [z0]
        rw [padZero_val_lt x _ (by omega)]
        exact congrArg x (Fin.ext (by dsimp; omega))
      · have hev : (emb u).1 = w + (u.1 - 1) / 2 := by simp [emb, h0, hm]
        have hu_lt : (u.1 - 1) / 2 < w := by have := u.isLt; omega
        rw [dif_neg hm]; dsimp only [z0]
        rw [padZero_val_lt x _ (by omega)]
        exact congrArg x (Fin.ext (by dsimp; omega))
  have hact_core := act_cuccaroCore_ket w false a b
  dsimp only at hact_core
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at hact_core
  have hact := act_mapWires_ket (cuccaroCore w) emb z0 _ (by rw [hz0_comp]; exact hact_core)
    (padZero (w + w) 1 (addInPlaceFn w x)) ?_ ?_
  · exact hact
  · funext u
    dsimp only [Function.comp_apply]
    by_cases h0 : u.1 = 0
    · rw [dif_pos h0]
      have hev : (emb u).1 = w + w := by simp [emb, h0]
      exact padZero_val_ge (addInPlaceFn w x) (emb u) (by omega)
    · rw [dif_neg h0]
      by_cases hm : (u.1 - 1) % 2 = 0
      · have hev : (emb u).1 = (u.1 - 1) / 2 := by simp [emb, h0, hm]
        have hu_lt : (u.1 - 1) / 2 < w := by have := u.isLt; omega
        rw [dif_pos hm, padZero_val_lt _ _ (by omega)]
        dsimp only [addInPlaceFn]; rw [dif_pos (by omega)]
        exact congrArg x (Fin.ext (by dsimp; omega))
      · have hev : (emb u).1 = w + (u.1 - 1) / 2 := by simp [emb, h0, hm]
        have hu_lt : (u.1 - 1) / 2 < w := by have := u.isLt; omega
        rw [dif_neg hm, padZero_val_lt _ _ (by omega)]
        dsimp only [addInPlaceFn]; rw [dif_neg (by omega)]
        exact congrArg (natToBitsLSB w (bitsToNatLSB a + bitsToNatLSB b)) (Fin.ext (by dsimp; omega))
  · intro u hu
    exfalso; apply hu
    have hlt := u.isLt
    by_cases huw : u.1 = w + w
    · exact ⟨0, Fin.ext (by simp [emb, huw])⟩
    · by_cases hw : u.1 < w
      · exact ⟨⟨1 + 2 * u.1, by omega⟩, Fin.ext (by simp [emb])⟩
      · exact ⟨⟨1 + 2 * (u.1 - w) + 1, by omega⟩, Fin.ext (by simp [emb]; omega)⟩

/-- In-place `w`-bit subtractor `(a, b) ↦ (a, (b - a) mod 2^w)` (`(addInPlaceCircuit w).adj`). -/
noncomputable def subInPlaceCircuit (w : ℕ) : LayeredCircuit ((w + w) + 1) :=
  (addInPlaceCircuit w).adj

lemma subInPlaceCircuit_size (w : ℕ) : (subInPlaceCircuit w).size = 14 * w := by
  simp [subInPlaceCircuit, addInPlaceCircuit_size]

def subInPlaceFn (w : ℕ) (x : Qubits (w + w)) : Qubits (w + w) :=
  let a : Qubits w := fun i => x ⟨i.1, by omega⟩
  let b : Qubits w := fun i => x ⟨w + i.1, by omega⟩
  let diff := natToBitsLSB w (2 ^ w + bitsToNatLSB b - bitsToNatLSB a)
  fun i => if h : i.1 < w then a ⟨i.1, h⟩ else diff ⟨i.1 - w, by omega⟩

lemma addInPlaceFn_subInPlaceFn (w : ℕ) (x : Qubits (w + w)) :
    addInPlaceFn w (subInPlaceFn w x) = x ∧ subInPlaceFn w (addInPlaceFn w x) = x := by
  let a : Qubits w := fun i => x ⟨i.1, by omega⟩
  let b : Qubits w := fun i => x ⟨w + i.1, by omega⟩
  have ha_lt := bitsToNatLSB_lt w a
  have hb_lt := bitsToNatLSB_lt w b
  have ha_s : (fun i : Fin w => subInPlaceFn w x ⟨i.1, by omega⟩) = a := by
    funext i; simp [subInPlaceFn, a, i.isLt]
  have hb_s : (fun i : Fin w => subInPlaceFn w x ⟨w + i.1, by omega⟩) =
      natToBitsLSB w (2 ^ w + bitsToNatLSB b - bitsToNatLSB a) := by
    funext i; simp [subInPlaceFn, a, b, show ¬ w + i.1 < w by omega]
  have ha_a : (fun i : Fin w => addInPlaceFn w x ⟨i.1, by omega⟩) = a := by
    funext i; simp [addInPlaceFn, a, i.isLt]
  have hb_a : (fun i : Fin w => addInPlaceFn w x ⟨w + i.1, by omega⟩) =
      natToBitsLSB w (bitsToNatLSB a + bitsToNatLSB b) := by
    funext i; simp [addInPlaceFn, a, b, show ¬ w + i.1 < w by omega]
  have hmod1 : (bitsToNatLSB a + (2 ^ w + bitsToNatLSB b - bitsToNatLSB a) % 2 ^ w) % 2 ^ w =
      bitsToNatLSB b := by
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
      show bitsToNatLSB a + (2 ^ w + bitsToNatLSB b - bitsToNatLSB a) = 2 ^ w + bitsToNatLSB b by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt hb_lt]
  have hmod2 : (2 ^ w + (bitsToNatLSB a + bitsToNatLSB b) % 2 ^ w - bitsToNatLSB a) % 2 ^ w =
      bitsToNatLSB b := by
    by_cases hsum : bitsToNatLSB a + bitsToNatLSB b < 2 ^ w
    · rw [Nat.mod_eq_of_lt hsum, show 2 ^ w + (bitsToNatLSB a + bitsToNatLSB b) - bitsToNatLSB a =
        2 ^ w + bitsToNatLSB b by omega, Nat.add_mod_left, Nat.mod_eq_of_lt hb_lt]
    · have hmod_eq : (bitsToNatLSB a + bitsToNatLSB b) % 2 ^ w =
          bitsToNatLSB a + bitsToNatLSB b - 2 ^ w := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [hmod_eq, show 2 ^ w + (bitsToNatLSB a + bitsToNatLSB b - 2 ^ w) - bitsToNatLSB a =
        bitsToNatLSB b by omega, Nat.mod_eq_of_lt hb_lt]
  have hntb_eq : ∀ u : ℕ, natToBitsLSB w (u % 2 ^ w) = natToBitsLSB w u := fun u => by
    funext i; simp [natToBitsLSB, Nat.testBit_mod_two_pow, i.isLt]
  constructor
  · funext i; by_cases hi : i.1 < w
    · simp [addInPlaceFn, subInPlaceFn, hi]
    · simp only [addInPlaceFn, hi, ↓reduceDIte, ha_s, hb_s]
      have h1 : bitsToNatLSB (natToBitsLSB w (2 ^ w + bitsToNatLSB b - bitsToNatLSB a)) =
          (2 ^ w + bitsToNatLSB b - bitsToNatLSB a) % 2 ^ w := by
        rw [← hntb_eq, bitsToNatLSB_natToBitsLSB (Nat.mod_lt _ (Nat.two_pow_pos w))]
      rw [h1, ← hntb_eq, hmod1, natToBitsLSB_bitsToNatLSB]
      have hie : b ⟨i.1 - w, by omega⟩ = x i := by
        dsimp only [b]; exact congrArg x (Fin.ext (by dsimp; omega))
      exact hie
  · funext i; by_cases hi : i.1 < w
    · simp [subInPlaceFn, addInPlaceFn, hi]
    · simp only [subInPlaceFn, hi, ↓reduceDIte, ha_a, hb_a]
      have h1 : bitsToNatLSB (natToBitsLSB w (bitsToNatLSB a + bitsToNatLSB b)) =
          (bitsToNatLSB a + bitsToNatLSB b) % 2 ^ w := by
        rw [← hntb_eq, bitsToNatLSB_natToBitsLSB (Nat.mod_lt _ (Nat.two_pow_pos w))]
      rw [h1, ← hntb_eq, hmod2, natToBitsLSB_bitsToNatLSB]
      have hie : b ⟨i.1 - w, by omega⟩ = x i := by
        dsimp only [b]; exact congrArg x (Fin.ext (by dsimp; omega))
      exact hie

theorem subInPlaceCircuit_implements (w : ℕ) :
    (subInPlaceCircuit w).ImplementsOnClean (permMat (subInPlaceFn w)) :=
  adj_implementsOnClean_perm (addInPlaceCircuit w)
    (fun x => (addInPlaceFn_subInPlaceFn w x).2)
    (fun x => (addInPlaceFn_subInPlaceFn w x).1)
    (addInPlaceCircuit_implements w)


def combineEmb {a b m : ℕ} (ea : Fin a ↪ Fin m) (eb : Fin b ↪ Fin m)
    (hdisj : ∀ i j, ea i ≠ eb j) : Fin (a + b) ↪ Fin m where
  toFun := Fin.addCases ea eb
  inj' x y h := by
    induction x using Fin.addCases with
    | left ix =>
      induction y using Fin.addCases with
      | left iy => simp only [Fin.addCases_left] at h; rw [ea.injective h]
      | right jy => simp only [Fin.addCases_left, Fin.addCases_right] at h; exact absurd h (hdisj ix jy)
    | right jx =>
      induction y using Fin.addCases with
      | left iy => simp only [Fin.addCases_right, Fin.addCases_left] at h; exact absurd h.symm (hdisj iy jx)
      | right jy => simp only [Fin.addCases_right] at h; rw [eb.injective h]

@[simp] lemma combineEmb_castAdd {a b m : ℕ} (ea : Fin a ↪ Fin m) (eb : Fin b ↪ Fin m)
    (hdisj : ∀ i j, ea i ≠ eb j) (i : Fin a) :
    combineEmb ea eb hdisj (Fin.castAdd b i) = ea i := by
  change Fin.addCases ea eb (Fin.castAdd b i) = ea i; simp

@[simp] lemma combineEmb_natAdd {a b m : ℕ} (ea : Fin a ↪ Fin m) (eb : Fin b ↪ Fin m)
    (hdisj : ∀ i j, ea i ≠ eb j) (j : Fin b) :
    combineEmb ea eb hdisj (Fin.natAdd a j) = eb j := by
  change Fin.addCases ea eb (Fin.natAdd a j) = eb j; simp

lemma castAddEmb_trans_combineEmb {a b m : ℕ} (ea : Fin a ↪ Fin m) (eb : Fin b ↪ Fin m)
    (hdisj : ∀ i j, ea i ≠ eb j) :
    (Fin.castAddEmb b).trans (combineEmb ea eb hdisj) = ea := by
  ext i; simp

lemma act_subReg_perm {main anc m : ℕ} (lc : LayeredCircuit (main + anc))
    (f : Qubits main → Qubits main) (hlc : lc.ImplementsOnClean (permMat f))
    (embMain : Fin main ↪ Fin m) (embAnc : Fin anc ↪ Fin m)
    (hdisj : ∀ i j, embMain i ≠ embAnc j) (z : Qubits m)
    (hclean : ∀ j : Fin anc, z (embAnc j) = false) :
    act (lc.mapWires (combineEmb embMain embAnc hdisj)).unitary (ket z) =
      ket (updateOn embMain z (f (z ∘ embMain))) := by
  have hact := act_mapWires_perm lc f hlc (combineEmb embMain embAnc hdisj) z
    (fun j => by simpa using hclean j)
  rwa [castAddEmb_trans_combineEmb] at hact

private noncomputable def ctrlCopyPrefixCircuit (w : ℕ) :
    (k : ℕ) → k ≤ w → LayeredCircuit (1 + w + w)
  | 0, _ => LayeredCircuit.id (1 + w + w)
  | k + 1, hk =>
    let prev := ctrlCopyPrefixCircuit w k (by omega)
    let c : Fin (1 + w + w) := ⟨0, by omega⟩
    let a : Fin (1 + w + w) := ⟨1 + k, by omega⟩
    let b : Fin (1 + w + w) := ⟨1 + w + k, by omega⟩
    have hca : c ≠ a := Fin.ne_of_val_ne (by dsimp [c, a]; omega)
    have hcb : c ≠ b := Fin.ne_of_val_ne (by dsimp [c, b]; omega)
    have hab : a ≠ b := Fin.ne_of_val_ne (by dsimp [a, b]; omega)
    prev.seq (toffoliOn c a b hca hcb hab)

private lemma ctrlCopyPrefixCircuit_size (w k : ℕ) (hk : k ≤ w) :
    (ctrlCopyPrefixCircuit w k hk).size = 5 * k := by
  induction k with
  | zero => simp [ctrlCopyPrefixCircuit]
  | succ k ih =>
    dsimp only [ctrlCopyPrefixCircuit]
    rw [LayeredCircuit.seq_size, ih (by omega), toffoliOn_size]
    omega

private lemma act_ctrlCopyPrefixCircuit_ket (w k : ℕ) (hk : k ≤ w) (z : Qubits (1 + w + w)) :
    act (ctrlCopyPrefixCircuit w k hk).unitary (ket z) =
      ket (fun u =>
        if z ⟨0, by omega⟩ then
          if h2 : 1 + w ≤ u.1 ∧ u.1 < 1 + w + k then
            xor (z u) (z ⟨u.1 - w, by omega⟩)
          else z u
        else z u) := by
  induction k with
  | zero =>
    simp only [ctrlCopyPrefixCircuit, LayeredCircuit.id_unitary, act_one]
    congr 1; funext u
    cases z ⟨0, by omega⟩
    · rfl
    · simp only [↓reduceIte]; rw [dif_neg (by omega)]
  | succ k ih =>
    dsimp only [ctrlCopyPrefixCircuit]
    rw [LayeredCircuit.seq_unitary, act_mul, ih (by omega), act_toffoliOn_ket]
    congr 1; funext u
    let c : Fin (1 + w + w) := ⟨0, by omega⟩
    let a : Fin (1 + w + w) := ⟨1 + k, by omega⟩
    let b : Fin (1 + w + w) := ⟨1 + w + k, by omega⟩
    have hc_v : c.1 = 0 := rfl
    have ha_v : a.1 = 1 + k := rfl
    have hb_v : b.1 = 1 + w + k := rfl
    by_cases hz0 : z ⟨0, by omega⟩ = true
    · have hzc_out : (if z ⟨0, by omega⟩ = true then
          if h2 : 1 + w ≤ c.1 ∧ c.1 < 1 + w + k then xor (z c) (z ⟨c.1 - w, by omega⟩) else z c
        else z c) = true := by
        rw [if_pos hz0, dif_neg (by omega)]; exact hz0
      have hza_out : (if z ⟨0, by omega⟩ = true then
          if h2 : 1 + w ≤ a.1 ∧ a.1 < 1 + w + k then xor (z a) (z ⟨a.1 - w, by omega⟩) else z a
        else z a) = z a := by
        rw [if_pos hz0, dif_neg (by omega)]
      have hz0' : z ⟨0, by omega⟩ = true := hz0
      rw [hzc_out, hza_out, if_pos hz0]
      by_cases hub : u = b
      · subst hub
        have hb_n : ¬ (1 + w ≤ b.1 ∧ b.1 < 1 + w + k) := by dsimp only [b]; omega
        have hb_new : 1 + w ≤ b.1 ∧ b.1 < 1 + w + (k + 1) := by dsimp only [b]; omega
        rw [Function.update_self, dif_neg hb_n, dif_pos hb_new]
        have hsub : (⟨b.1 - w, by omega⟩ : Fin (1 + w + w)) = a := Fin.ext (by dsimp only [a, b]; omega)
        rw [hsub]
        rw [if_pos hz0']
        rfl
      · rw [Function.update_of_ne hub]
        by_cases h2 : 1 + w ≤ u.1 ∧ u.1 < 1 + w + k
        · rw [dif_pos h2, dif_pos (by omega)]
        · have h2' : ¬ (1 + w ≤ u.1 ∧ u.1 < 1 + w + (k + 1)) := by
            intro h; apply hub; apply Fin.ext; omega
          rw [dif_neg h2, dif_neg h2']
    · have hzc_out : (if z ⟨0, by omega⟩ = true then
          if h2 : 1 + w ≤ c.1 ∧ c.1 < 1 + w + k then xor (z c) (z ⟨c.1 - w, by omega⟩) else z c
        else z c) = false := by
        rw [if_neg hz0]
        cases hz_c : z ⟨0, by omega⟩
        · rfl
        · exact absurd hz_c hz0
      rw [hzc_out, Bool.false_and, Bool.xor_false, Function.update_eq_self, if_neg hz0, if_neg hz0]

/-- Controlled bitwise copy `(ctrl, a, b) ↦ (ctrl, a, if ctrl then b ^^^ a else b)` in `5 * w` gates. -/
noncomputable def ctrlCopyRegCircuit (w : ℕ) : LayeredCircuit ((1 + w + w) + 0) :=
  ctrlCopyPrefixCircuit w w le_rfl

lemma ctrlCopyRegCircuit_size (w : ℕ) : (ctrlCopyRegCircuit w).size = 5 * w :=
  ctrlCopyPrefixCircuit_size w w le_rfl

def ctrlCopyRegFn (w : ℕ) (x : Qubits (1 + w + w)) : Qubits (1 + w + w) :=
  fun u =>
    if x ⟨0, by omega⟩ then
      if h : 1 + w ≤ u.1 then xor (x u) (x ⟨u.1 - w, by omega⟩) else x u
    else x u

theorem ctrlCopyRegCircuit_implements (w : ℕ) :
    (ctrlCopyRegCircuit w).ImplementsOnClean (permMat (ctrlCopyRegFn w)) := by
  apply implementsOnClean_of_act_perm
  intro x
  dsimp only [ctrlCopyRegCircuit]
  have h0 : padZero (1 + w + w) 0 x = x := by funext u; simp
  have h0' : padZero (1 + w + w) 0 (ctrlCopyRegFn w x) = ctrlCopyRegFn w x := by funext u; simp
  rw [h0, h0', act_ctrlCopyPrefixCircuit_ket]
  congr 1; funext u
  have hu := u.isLt
  by_cases hx : x ⟨0, by omega⟩ = true
  · dsimp only [ctrlCopyRegFn]; rw [if_pos hx, if_pos hx]
    by_cases h2 : 1 + w ≤ u.1
    · rw [dif_pos ⟨h2, hu⟩, dif_pos h2]
    · rw [dif_neg (by omega), dif_neg h2]
  · dsimp only [ctrlCopyRegFn]; rw [if_neg hx, if_neg hx]


private lemma act_subReg_perm_54 {main anc m : ℕ} (lc : LayeredCircuit (main + anc))
    (f : Qubits main → Qubits main) (hlc : lc.ImplementsOnClean (permMat f))
    (embMain : Fin main ↪ Fin m) (embAnc : Fin anc ↪ Fin m)
    (hdisj : ∀ i j, embMain i ≠ embAnc j) (z : Qubits m)
    (hclean : ∀ j : Fin anc, z (embAnc j) = false) :
    act (lc.mapWires (combineEmb54 embMain embAnc hdisj)).unitary (ket z) =
      ket (updateOn embMain z (f (z ∘ embMain))) := by
  have hact := act_mapWires_perm lc f hlc (combineEmb54 embMain embAnc hdisj) z
    (fun j => by simpa using hclean j)
  have hemb : (Fin.castAddEmb anc).trans (combineEmb54 embMain embAnc hdisj) = embMain := by
    ext i; simp
  rwa [hemb] at hact

end OccArithImpl

end QuantumLTF.Membership.Supplement

open QuantumLTF.Membership.Supplement

theorem solution : Nonempty OccArith54 := ⟨{
  prefSum_eq_excl_add := OccArithImpl.prefSum_eq_excl_add
  prefSum_mono := OccArithImpl.prefSum_mono
  exclPrefSum_le_prefSum_of_lt := OccArithImpl.exclPrefSum_le_prefSum_of_lt
  exclPrefSum_zero := OccArithImpl.exclPrefSum_zero
  prefSum_last := OccArithImpl.prefSum_last
  prefSum_le_sum := OccArithImpl.prefSum_le_sum
  modeOf_lt := OccArithImpl.modeOf_lt
  modeOf_spec := OccArithImpl.modeOf_spec
  modeOf_eq_iff := OccArithImpl.modeOf_eq_iff
  modeOf_count := OccArithImpl.modeOf_count
  modeOf_mono := OccArithImpl.modeOf_mono
  wtilde2_length := OccArithImpl.wtilde2_length
  wtilde3_length := OccArithImpl.wtilde3_length
  wtilde8_length := OccArithImpl.wtilde854_length
  wtildef_length := OccArithImpl.wtildef54_length
  wtilde3_pos_spec := OccArithImpl.wtilde3_pos_spec
  wtilde8_pos_spec := OccArithImpl.wtilde8_pos_spec_54
  wtilde2_sort_prefix := OccArithImpl.wtilde2_sort_prefix_54
  wtildef_sort_prefix := OccArithImpl.wtildef_sort_prefix_54
  permMat_id := OccArithImpl.permMat_id
  permMat_mul := OccArithImpl.permMat_mul
  seqClean_perm := OccArithImpl.seqClean_perm
  adj_implementsOnClean_perm := OccArithImpl.adj_implementsOnClean_perm
  act_mapWires_perm := OccArithImpl.act_mapWires_perm
  act_subReg_perm := OccArithImpl.act_subReg_perm_54
  padZero_val_lt := OccArithImpl.padZero_val_lt
  padZero_val_ge := OccArithImpl.padZero_val_ge
  bitsToNatLSB_rev := OccArithImpl.bitsToNatLSB_rev
  natToBits_eq_rev_natToBitsLSB := OccArithImpl.natToBits_eq_rev_natToBitsLSB
  natToBits_apply := OccArithImpl.natToBits_apply
  bitsToNatLSB_all_false := OccArithImpl.bitsToNatLSB_all_false
  copyRegCircuit := OccArithImpl.copyRegCircuit
  copyRegCircuit_size := OccArithImpl.copyRegCircuit_size
  copyRegCircuit_implements := fun w => OccArithImpl.copyRegCircuit_implements w
  setConstCircuit := OccArithImpl.setConstCircuit
  setConstCircuit_size := OccArithImpl.setConstCircuit_size
  setConstCircuit_implements := fun w c => OccArithImpl.setConstCircuit_implements w c
  eqConstCircuit := OccArithImpl.eqConstCircuit
  eqConstCircuit_size := OccArithImpl.eqConstCircuit_size
  eqConstCircuit_implements := fun w c => OccArithImpl.eqConstCircuit_implements w c
  addInPlaceCircuit := OccArithImpl.addInPlaceCircuit
  addInPlaceCircuit_size := OccArithImpl.addInPlaceCircuit_size
  addInPlaceCircuit_implements := fun w => OccArithImpl.addInPlaceCircuit_implements w
  subInPlaceCircuit := OccArithImpl.subInPlaceCircuit
  subInPlaceCircuit_size := OccArithImpl.subInPlaceCircuit_size
  subInPlaceCircuit_implements := fun w => OccArithImpl.subInPlaceCircuit_implements w
  ctrlCopyRegCircuit := OccArithImpl.ctrlCopyRegCircuit
  ctrlCopyRegCircuit_size := OccArithImpl.ctrlCopyRegCircuit_size
  ctrlCopyRegCircuit_implements := fun w => OccArithImpl.ctrlCopyRegCircuit_implements w
  encodeParticleSym54Circuit := OccArithImpl.encodeParticleSym54Circuit
  encodeParticleSym54Circuit_size := OccArithImpl.encodeParticleSym54Circuit_size
  encodeParticleSym54Circuit_act := OccArithImpl.encodeParticleSym54Circuit_act
}⟩
