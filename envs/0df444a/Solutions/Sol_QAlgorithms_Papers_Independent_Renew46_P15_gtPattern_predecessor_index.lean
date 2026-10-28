-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P15.gtPattern_predecessor_index
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T06:31:05.330008+00:00
-- url     : https://prove2.me/submissions/8623d88d-788e-45b3-b791-97f6c487d6fe

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P15

noncomputable section

open scoped BigOperators Matrix

namespace QAlgorithms.Papers.Independent.Renew46.P15

attribute [local instance] Classical.propDecidable

section GTAux
open OrderDual
variable {n : ℕ}

/-- top row extended by zero -/
def sN (s : GTTopRow n) (k : ℕ) : ℕ := if h : k < n + 2 then s.val ⟨k, h⟩ else 0

lemma sN_anti (s : GTTopRow n) {a b : ℕ} (h : a ≤ b) : sN s b ≤ sN s a := by
  unfold sN
  by_cases hb : b < n + 2
  · have ha : a < n + 2 := by omega
    simp only [hb, ha, dite_true]
    exact s.property.1 (by exact_mod_cast h)
  · simp [hb]

def gg {s : GTTopRow n} (m : Pattern s) (l k : ℕ) : ℕ := gridEntry (patternGrid m) l k

lemma gg_big {s : GTTopRow n} (m : Pattern s) {l k : ℕ} (h : ¬ (l < n + 2 ∧ k < n + 2)) :
    gg m l k = 0 := by simp [gg, gridEntry, h]

lemma gg_in {s : GTTopRow n} (m : Pattern s) {l k : ℕ} (hl : l < n + 2) (hk : k < n + 2) :
    gg m l k = (m.val ⟨l, hl⟩ ⟨k, hk⟩).val := by
  simp [gg, gridEntry, patternGrid, hl, hk]

lemma gg_top {s : GTTopRow n} (m : Pattern s) (k : ℕ) : gg m (n + 1) k = sN s k := by
  by_cases hk : k < n + 2
  · rw [gg_in m (by omega) hk]
    have := m.property.1 ⟨k, hk⟩
    simp only [sN, hk, dite_true]
    exact this
  · rw [gg_big m (by omega)]; simp [sN, hk]

lemma gg_zero {s : GTTopRow n} (m : Pattern s) {l k : ℕ} (h : l < k) : gg m l k = 0 := by
  by_cases hk : l < n + 2 ∧ k < n + 2
  · rw [gg_in m hk.1 hk.2]
    have := m.property.2.1 ⟨l, hk.1⟩ ⟨k, hk.2⟩ (by exact_mod_cast h)
    simpa using this
  · exact gg_big m hk

lemma gg_betw {s : GTTopRow n} (m : Pattern s) {l k : ℕ} (hl : l + 1 < n + 2) (hk : k ≤ l) :
    gg m l k ≤ gg m (l + 1) k ∧ gg m (l + 1) (k + 1) ≤ gg m l k := by
  have := m.property.2.2 l k hl hk
  exact ⟨this.1, this.2⟩

lemma gg_ext {s : GTTopRow n} {m m' : Pattern s} (h : ∀ l k, gg m l k = gg m' l k) : m = m' := by
  apply Subtype.ext
  funext l k
  apply Fin.ext
  have := h l.val k.val
  rwa [gg_in m l.isLt k.isLt, gg_in m' l.isLt k.isLt] at this

lemma gg_le_sN {s : GTTopRow n} (m : Pattern s) :
    ∀ d l k, l + d = n + 1 → gg m l k ≤ sN s k := by
  intro d
  induction d with
  | zero => intro l k h; have : l = n + 1 := by omega
            subst this; rw [gg_top]
  | succ d ih =>
    intro l k h
    by_cases hk : k ≤ l
    · have h1 := (gg_betw m (l := l) (k := k) (by omega) hk).1
      have h2 := ih (l + 1) k (by omega)
      omega
    · rw [gg_zero m (by omega)]; omega

lemma gg_le_sN0 {s : GTTopRow n} (m : Pattern s) (l k : ℕ) : gg m l k ≤ sN s 0 := by
  by_cases hl : l ≤ n + 1
  · exact (gg_le_sN m (n + 1 - l) l k (by omega)).trans (sN_anti s (Nat.zero_le _))
  · rw [gg_big m (by omega)]; omega

lemma sN_le_gg {s : GTTopRow n} (m : Pattern s) :
    ∀ d l k, l + d = n + 1 → k ≤ l → sN s (k + d) ≤ gg m l k := by
  intro d
  induction d with
  | zero => intro l k h _; have : l = n + 1 := by omega
            subst this; simp [gg_top]
  | succ d ih =>
    intro l k h hk
    have h1 := (gg_betw m (l := l) (k := k) (by omega) hk).2
    have h2 := ih (l + 1) (k + 1) (by omega) (by omega)
    have : k + 1 + d = k + (d + 1) := by omega
    rw [this] at h2
    omega

/-- build a pattern from an unbounded grid -/
def mkPat (s : GTTopRow n) (G : ℕ → ℕ → ℕ) (h1 : ∀ k, G (n + 1) k = sN s k)
    (h2 : ∀ l k, l < k → G l k = 0)
    (h3 : ∀ l k, l + 1 < n + 2 → k ≤ l → G l k ≤ G (l + 1) k ∧ G (l + 1) (k + 1) ≤ G l k)
    (h5 : ∀ l k, G l k ≤ sN s 0) : Pattern s :=
  ⟨fun l k => ⟨G l.val k.val, by
      have := h5 l.val k.val
      have h0 : sN s 0 = s.val 0 := by simp [sN]
      omega⟩, by
    refine ⟨?_, ?_, ?_⟩
    · intro k; simp [h1, sN]
    · intro l k h; simp [h2 _ _ (by exact_mod_cast h)]
    · intro l k hl hk
      have e : ∀ a b : ℕ, a < n + 2 → b < n + 2 →
          gridEntry (fun l k : Fin (n+2) => G l.val k.val) a b = G a b := by
        intro a b ha hb; simp [gridEntry, ha, hb]
      have := h3 l k hl hk
      have hl' : l + 1 < n + 2 := hl
      show gridEntry (fun l k : Fin (n+2) => G l.val k.val) (l+1) k ≥ gridEntry (fun l k : Fin (n+2) => G l.val k.val) l k ∧ _
      rw [e (l+1) k hl' (by omega), e l k (by omega) (by omega), e (l+1) (k+1) hl' (by omega)]
      exact this⟩

lemma gg_mkPat (s : GTTopRow n) (G : ℕ → ℕ → ℕ) (h1 : ∀ k, G (n + 1) k = sN s k)
    (h2 : ∀ l k, l < k → G l k = 0)
    (h3 : ∀ l k, l + 1 < n + 2 → k ≤ l → G l k ≤ G (l + 1) k ∧ G (l + 1) (k + 1) ≤ G l k)
    (h4 : ∀ l k, ¬ (l < n + 2 ∧ k < n + 2) → G l k = 0)
    (h5 : ∀ l k, G l k ≤ sN s 0) (l k : ℕ) :
    gg (mkPat s G h1 h2 h3 h5) l k = G l k := by
  by_cases h : l < n + 2 ∧ k < n + 2
  · rw [gg_in _ h.1 h.2]; rfl
  · rw [gg_big _ h, h4 _ _ h]

abbrev Idx (n : ℕ) := OrderDual (Fin (n + 2)) ×ₗ Fin (n + 2)

lemma pg_eq {s : GTTopRow n} (m : Pattern s) (l k : Fin (n + 2)) :
    patternGrid m l k = gg m l.val k.val := by
  rw [gg_in m l.isLt k.isLt]; rfl

def FF {s : GTTopRow n} (m : Pattern s) : Idx n → ℕ :=
  fun i => gg m (ofDual (ofLex i).1).val (ofLex i).2.val

lemma FF_injective {s : GTTopRow n} : Function.Injective (FF (s := s)) := by
  intro a b h
  apply gg_ext
  intro l k
  by_cases hh : l < n + 2 ∧ k < n + 2
  · have := congrFun h (toLex (toDual ⟨l, hh.1⟩, ⟨k, hh.2⟩))
    simpa [FF] using this
  · rw [gg_big a hh, gg_big b hh]

lemma patternLt_iff {s : GTTopRow n} (a b : Pattern s) :
    patternLt a b ↔ toLex (FF a) < toLex (FF b) := by
  constructor
  · rintro ⟨p, hp, hbefore, hlt⟩
    refine ⟨toLex (toDual p.1, p.2), ?_, ?_⟩
    · intro j hj
      obtain ⟨⟨l', k'⟩, rfl⟩ : ∃ x, j = toLex x := ⟨ofLex j, rfl⟩
      rw [Prod.Lex.lt_iff] at hj
      simp only [ofLex_toLex] at hj
      by_cases hk : k' ≤ ofDual l'
      · have := hbefore (ofDual l', k') hk (by
          rcases hj with hj | ⟨hj1, hj2⟩
          · left; exact hj
          · right; exact ⟨by rw [hj1]; rfl, hj2⟩)
        rw [pg_eq, pg_eq] at this
        simpa [FF] using this
      · have h1 : (ofDual l').val < k'.val := by
          have := not_le.mp hk; exact this
        show FF a (toLex (l', k')) = FF b (toLex (l', k'))
        simp only [FF, ofLex_toLex]
        rw [gg_zero a h1, gg_zero b h1]
    · rw [pg_eq, pg_eq] at hlt
      simpa [FF] using hlt
  · rintro ⟨i, hi1, hi2⟩
    obtain ⟨⟨l', k'⟩, rfl⟩ : ∃ x, i = toLex x := ⟨ofLex i, rfl⟩
    have hi1' : ∀ j : Idx n, j < toLex (l', k') → FF a j = FF b j := hi1
    have hi2' : FF a (toLex (l', k')) < FF b (toLex (l', k')) := hi2
    clear hi1 hi2
    have hk : k' ≤ ofDual l' := by
      by_contra hk
      have h1 : (ofDual l').val < k'.val := not_le.mp hk
      simp only [FF, ofLex_toLex] at hi2'
      rw [gg_zero a h1, gg_zero b h1] at hi2'
      exact lt_irrefl _ hi2'
    refine ⟨(ofDual l', k'), hk, ?_, ?_⟩
    · intro q hq hqp
      have := hi1' (toLex (toDual q.1, q.2)) (by
        show toLex (toDual q.1, q.2) < toLex (l', k')
        rw [Prod.Lex.lt_iff]
        rcases hqp with h | ⟨h1, h2⟩
        · left; exact h
        · right; exact ⟨by simp [h1], h2⟩)
      rw [pg_eq, pg_eq]
      simpa [FF] using this
    · rw [pg_eq, pg_eq]
      simpa [FF] using hi2'


variable {s : GTTopRow n}

lemma plt_irrefl (a : Pattern s) : ¬ patternLt a a := by
  rw [patternLt_iff]; exact lt_irrefl _

lemma plt_trans {a b c : Pattern s} (h1 : patternLt a b) (h2 : patternLt b c) : patternLt a c := by
  rw [patternLt_iff] at *; exact lt_trans h1 h2

lemma plt_trich (a b : Pattern s) : patternLt a b ∨ a = b ∨ patternLt b a := by
  simp only [patternLt_iff]
  rcases lt_trichotomy (toLex (FF a)) (toLex (FF b)) with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (FF_injective (toLex.injective h)))
  · exact Or.inr (Or.inr h)

lemma plt_of_le_ne (a b : Pattern s) (h : ∀ l k, gg a l k ≤ gg b l k) (hne : a ≠ b) :
    patternLt a b := by
  rw [patternLt_iff]
  apply Pi.toLex_strictMono
  refine lt_of_le_of_ne (fun i => ?_) (fun h' => hne (FF_injective h'))
  exact h _ _

lemma rank_lt {a b : Pattern s} (h : patternLt a b) : patternRank a < patternRank b := by
  unfold patternRank
  have : (Finset.univ.filter fun p : Pattern s => patternLt p a) ⊂
      (Finset.univ.filter fun p : Pattern s => patternLt p b) := by
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨a, by simp [h], by simp [plt_irrefl]⟩
    · intro x hx; simp at hx ⊢; exact plt_trans hx h
  have := Finset.card_lt_card this; omega

lemma rank_inj : Function.Injective (patternRank (s := s)) := by
  intro a b h
  rcases plt_trich a b with h1 | h1 | h1
  · exact absurd h (ne_of_lt (rank_lt h1))
  · exact h1
  · exact absurd h (ne_of_gt (rank_lt h1))

lemma rank_lt_iff (a b : Pattern s) : patternLt a b ↔ patternRank a < patternRank b := by
  constructor
  · exact rank_lt
  · intro h
    rcases plt_trich a b with h1 | h1 | h1
    · exact h1
    · subst h1; exact absurd h (lt_irrefl _)
    · exact absurd (rank_lt h1) (not_lt.mpr h.le)

lemma rank_pos (m : Pattern s) : 1 ≤ patternRank m := by unfold patternRank; omega

lemma rank_le_card (m : Pattern s) : patternRank m ≤ Fintype.card (Pattern s) := by
  unfold patternRank
  have : (Finset.univ.filter fun p : Pattern s => patternLt p m) ⊂ Finset.univ := by
    rw [Finset.ssubset_iff_of_subset (Finset.subset_univ _)]
    exact ⟨m, by simp, by simp [plt_irrefl]⟩
  have := Finset.card_lt_card this
  simp at this
  omega

lemma rank_surj (q : ℕ) (h1 : 1 ≤ q) (h2 : q ≤ Fintype.card (Pattern s)) :
    ∃ m : Pattern s, patternRank m = q := by
  let f : Pattern s → Fin (Fintype.card (Pattern s)) :=
    fun m => ⟨patternRank m - 1, by have := rank_le_card m; have := rank_pos m; omega⟩
  have hf : Function.Injective f := by
    intro a b h
    apply rank_inj
    have := rank_pos a; have := rank_pos b
    have h' : patternRank a - 1 = patternRank b - 1 := by simpa [f] using h
    omega
  have hb : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, by simp⟩
  obtain ⟨m, hm⟩ := hb.2 ⟨q - 1, by omega⟩
  refine ⟨m, ?_⟩
  have h' : patternRank m - 1 = q - 1 := by simpa [f] using hm
  have := rank_pos m
  omega


/-! minimal and maximal patterns -/

def G0 (s : GTTopRow n) (l k : ℕ) : ℕ := if k ≤ l ∧ l ≤ n + 1 then sN s (k + (n + 1 - l)) else 0

lemma G0_h1 (k : ℕ) : G0 s (n + 1) k = sN s k := by
  unfold G0
  by_cases hk : k ≤ n + 1
  · simp [hk]
  · have : sN s k = 0 := by simp [sN]; omega
    simp [hk, this]

lemma G0_h2 (l k : ℕ) (h : l < k) : G0 s l k = 0 := by
  unfold G0; rw [if_neg (by omega)]

lemma G0_h3 (l k : ℕ) (hl : l + 1 < n + 2) (hk : k ≤ l) :
    G0 s l k ≤ G0 s (l + 1) k ∧ G0 s (l + 1) (k + 1) ≤ G0 s l k := by
  unfold G0
  rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
  constructor
  · exact sN_anti s (by omega)
  · have : k + 1 + (n + 1 - (l + 1)) = k + (n + 1 - l) := by omega
    rw [this]

lemma G0_h4 (l k : ℕ) (h : ¬ (l < n + 2 ∧ k < n + 2)) : G0 s l k = 0 := by
  unfold G0; rw [if_neg (by omega)]

lemma G0_h5 (l k : ℕ) : G0 s l k ≤ sN s 0 := by
  unfold G0
  split_ifs
  · exact sN_anti s (Nat.zero_le _)
  · omega

def Pmin (s : GTTopRow n) : Pattern s := mkPat s (G0 s) G0_h1 G0_h2 G0_h3 G0_h5

lemma gg_Pmin (l k : ℕ) : gg (Pmin s) l k = G0 s l k :=
  gg_mkPat s (G0 s) G0_h1 G0_h2 G0_h3 G0_h4 G0_h5 l k

def GT (s : GTTopRow n) (l k : ℕ) : ℕ := if k ≤ l ∧ l ≤ n + 1 then sN s k else 0

lemma GT_h1 (k : ℕ) : GT s (n + 1) k = sN s k := by
  unfold GT
  by_cases hk : k ≤ n + 1
  · simp [hk]
  · have : sN s k = 0 := by simp [sN]; omega
    simp [hk, this]

lemma GT_h2 (l k : ℕ) (h : l < k) : GT s l k = 0 := by
  unfold GT; rw [if_neg (by omega)]

lemma GT_h3 (l k : ℕ) (hl : l + 1 < n + 2) (hk : k ≤ l) :
    GT s l k ≤ GT s (l + 1) k ∧ GT s (l + 1) (k + 1) ≤ GT s l k := by
  unfold GT
  rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
  exact ⟨le_rfl, sN_anti s (by omega)⟩

lemma GT_h4 (l k : ℕ) (h : ¬ (l < n + 2 ∧ k < n + 2)) : GT s l k = 0 := by
  unfold GT; rw [if_neg (by omega)]

lemma GT_h5 (l k : ℕ) : GT s l k ≤ sN s 0 := by
  unfold GT
  split_ifs
  · exact sN_anti s (Nat.zero_le _)
  · omega

def Ptop (s : GTTopRow n) : Pattern s := mkPat s (GT s) GT_h1 GT_h2 GT_h3 GT_h5

lemma gg_Ptop (l k : ℕ) : gg (Ptop s) l k = GT s l k :=
  gg_mkPat s (GT s) GT_h1 GT_h2 GT_h3 GT_h4 GT_h5 l k

lemma Pmin_le (m : Pattern s) (l k : ℕ) : gg (Pmin s) l k ≤ gg m l k := by
  rw [gg_Pmin]; unfold G0
  split_ifs with h
  · exact sN_le_gg m (n + 1 - l) l k (by omega) h.1
  · omega

lemma le_Ptop (m : Pattern s) (l k : ℕ) : gg m l k ≤ gg (Ptop s) l k := by
  rw [gg_Ptop]; unfold GT
  split_ifs with h
  · exact gg_le_sN m (n + 1 - l) l k (by omega)
  · by_cases hl : l ≤ n + 1
    · have : l < k := by omega
      rw [gg_zero m this]
    · rw [gg_big m (by omega)]

lemma rank_eq_one_iff (m : Pattern s) : patternRank m = 1 ↔ m = Pmin s := by
  constructor
  · intro h
    by_contra hne
    have hlt : patternLt (Pmin s) m := plt_of_le_ne _ _ (Pmin_le m) (Ne.symm hne)
    have := rank_lt hlt
    have := rank_pos (Pmin s)
    omega
  · rintro rfl
    unfold patternRank
    have : (Finset.univ.filter fun p : Pattern s => patternLt p (Pmin s)) = ∅ := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro hp
      by_cases hne : p = Pmin s
      · subst hne; exact plt_irrefl _ hp
      · have := plt_of_le_ne _ _ (Pmin_le p) (Ne.symm hne)
        exact plt_irrefl _ (plt_trans hp this)
    rw [this]; simp

lemma rank_eq_card_iff (m : Pattern s) : patternRank m = Fintype.card (Pattern s) ↔ m = Ptop s := by
  constructor
  · intro h
    by_contra hne
    have hlt : patternLt m (Ptop s) := plt_of_le_ne _ _ (le_Ptop m) hne
    have := rank_lt hlt
    have := rank_le_card (Ptop s)
    omega
  · rintro rfl
    unfold patternRank
    have : (Finset.univ.filter fun p : Pattern s => patternLt p (Ptop s)) = Finset.univ.erase (Ptop s) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq]
      constructor
      · intro hp; exact ⟨fun hh => by subst hh; exact plt_irrefl _ hp, trivial⟩
      · intro hp; exact plt_of_le_ne _ _ (fun l k => le_Ptop p l k) hp.1
    rw [this, Finset.card_erase_of_mem (Finset.mem_univ _)]
    have : 0 < Fintype.card (Pattern s) := Fintype.card_pos_iff.mpr ⟨Ptop s⟩
    simp; omega


/-! positions list and pivot -/

lemma gg_row_anti (m : Pattern s) (l k : ℕ) : gg m l (k + 1) ≤ gg m l k := by
  by_cases hl : l ≤ n
  · by_cases hk : k + 1 ≤ l
    · have h1 := gg_betw m (l := l) (k := k + 1) (by omega) hk
      have h2 := gg_betw m (l := l) (k := k) (by omega) (by omega)
      omega
    · rw [gg_zero m (by omega)]; omega
  · by_cases hl1 : l = n + 1
    · subst hl1; rw [gg_top, gg_top]; exact sN_anti s (by omega)
    · rw [gg_big m (by omega)]; omega

lemma mem_positions (p : Fin (n + 2) × Fin (n + 2)) :
    p ∈ patternPositions n ↔ p.2 ≤ p.1 := by
  unfold patternPositions
  simp only [List.mem_flatMap, List.mem_reverse, List.mem_finRange, true_and, List.mem_map]
  constructor
  · rintro ⟨l, k, rfl⟩
    show (⟨k.val, _⟩ : Fin (n+2)) ≤ l
    exact Nat.lt_succ_iff.mp k.isLt
  · intro h
    refine ⟨p.1, ⟨p.2.val, Nat.lt_succ_iff.mpr h⟩, ?_⟩
    rfl

lemma positions_pairwise : (patternPositions n).Pairwise positionLt := by
  unfold patternPositions
  rw [List.pairwise_flatMap]
  constructor
  · intro l _
    rw [List.pairwise_map]
    apply (List.pairwise_lt_finRange _).imp
    intro a b h
    right
    exact ⟨rfl, h⟩
  · rw [List.pairwise_reverse]
    apply (List.pairwise_lt_finRange _).imp
    intro a b h x hx y hy
    simp only [List.mem_map] at hx hy
    obtain ⟨_, _, rfl⟩ := hx
    obtain ⟨_, _, rfl⟩ := hy
    left
    exact h


def PP (m : Pattern s) (p : Fin (n + 2) × Fin (n + 2)) : Prop :=
  p.1.val < n + 1 ∧ gg m (p.1.val + 1) (p.2.val + 1) < gg m p.1.val p.2.val

lemma decide_PP (m : Pattern s) (p : Fin (n + 2) × Fin (n + 2)) :
    (decide (p.1.val < n + 1 ∧ gridEntry (patternGrid m) (p.1.val + 1) (p.2.val + 1) <
      patternGrid m p.1 p.2) = true) ↔ PP m p := by
  rw [decide_eq_true_eq, pg_eq]; rfl

lemma positionLt_asymm {p q : Fin (n + 2) × Fin (n + 2)} (h1 : positionLt p q) (h2 : positionLt q p) :
    False := by
  simp only [positionLt, Fin.lt_def, Fin.ext_iff] at h1 h2
  omega

lemma positionLt_irrefl (p : Fin (n + 2) × Fin (n + 2)) : ¬ positionLt p p := by
  simp only [positionLt, Fin.lt_def]
  omega

lemma pivot_some (m : Pattern s) (q : Fin (n + 2) × Fin (n + 2))
    (h : predecessorPivot m = some q) :
    PP m q ∧ q.2 ≤ q.1 ∧ ∀ r : Fin (n + 2) × Fin (n + 2), r.2 ≤ r.1 → positionLt q r → ¬ PP m r := by
  unfold predecessorPivot at h
  rw [List.find?_eq_some_iff_append] at h
  obtain ⟨hq, as, bs, hL, has⟩ := h
  have hP : patternPositions n = bs.reverse ++ q :: as.reverse := by
    rw [← List.reverse_reverse (patternPositions n), hL]; simp
  have hpw := positions_pairwise (n := n)
  rw [hP, List.pairwise_append] at hpw
  have hqmem : q ∈ patternPositions n := by
    rw [hP]; simp
  refine ⟨(decide_PP m q).mp hq, (mem_positions q).mp hqmem, ?_⟩
  intro r hr hqr hPr
  have hrmem : r ∈ patternPositions n := (mem_positions r).mpr hr
  rw [hP] at hrmem
  simp only [List.mem_append, List.mem_cons, List.mem_reverse] at hrmem
  rcases hrmem with h1 | h1 | h1
  · have := hpw.2.2 r (by simpa using h1) q (by simp)
    exact positionLt_asymm hqr this
  · subst h1; exact positionLt_irrefl _ hqr
  · have := has r h1
    simp only [Bool.not_eq_true'] at this
    have h3 : ¬ (decide (r.1.val < n + 1 ∧ gridEntry (patternGrid m) (r.1.val + 1) (r.2.val + 1) <
      patternGrid m r.1 r.2) = true) := by simpa using this
    exact h3 ((decide_PP m r).mpr hPr)

lemma pivot_none (m : Pattern s) (h : predecessorPivot m = none) (r : Fin (n + 2) × Fin (n + 2))
    (hr : r.2 ≤ r.1) : ¬ PP m r := by
  unfold predecessorPivot at h
  rw [List.find?_eq_none] at h
  intro hP
  exact h r (by rw [List.mem_reverse]; exact (mem_positions r).mpr hr) ((decide_PP m r).mpr hP)


lemma none_min (m : Pattern s) (h : ∀ r : Fin (n + 2) × Fin (n + 2), r.2 ≤ r.1 → ¬ PP m r) :
    m = Pmin s := by
  have key : ∀ d l k, l + d = n + 1 → k ≤ l → gg m l k ≤ sN s (k + d) := by
    intro d
    induction d with
    | zero => intro l k hl _; have : l = n + 1 := by omega
              subst this; simp [gg_top]
    | succ d ih =>
      intro l k hl hk
      have h1 := h (⟨l, by omega⟩, ⟨k, by omega⟩) (by exact hk)
      simp only [PP, not_and, not_lt] at h1
      have h2 := h1 (by show l < n + 1; omega)
      have h3 := ih (l + 1) (k + 1) (by omega) (by omega)
      have : k + 1 + d = k + (d + 1) := by omega
      rw [this] at h3
      omega
  apply gg_ext
  intro l k
  rw [gg_Pmin]
  unfold G0
  split_ifs with hh
  · exact le_antisymm (key (n + 1 - l) l k (by omega) hh.1) (sN_le_gg m (n + 1 - l) l k (by omega) hh.1)
  · by_cases hl : l ≤ n + 1
    · rw [gg_zero m (by omega)]
    · rw [gg_big m (by omega)]

structure PivCtx (m : Pattern s) (l0 k0 : ℕ) : Prop where
  hl0 : l0 ≤ n
  hk0 : k0 ≤ l0
  hpiv : gg m (l0 + 1) (k0 + 1) < gg m l0 k0
  hafter : ∀ l k, k ≤ l → l ≤ n → (l < l0 ∨ (l = l0 ∧ k0 < k)) → gg m l k ≤ gg m (l + 1) (k + 1)

def Up (m : Pattern s) (l0 k0 k : ℕ) : ℕ :=
  if k < k0 then gg m l0 k else if k = k0 then gg m l0 k0 - 1 else gg m (l0 + 1) k

def Rc (m : Pattern s) (l0 k0 l k : ℕ) : ℕ :=
  if l < k then 0 else
  if l0 < l ∨ (l = l0 ∧ k < k0) then gg m l k else Up m l0 k0 k

lemma Up_anti (m : Pattern s) {l0 k0 : ℕ} (C : PivCtx m l0 k0) (k : ℕ) :
    Up m l0 k0 (k + 1) ≤ Up m l0 k0 k := by
  have h1 := gg_row_anti m l0 k
  have h2 := gg_row_anti m (l0 + 1) k
  have h3 := C.hpiv
  unfold Up
  split_ifs <;> subst_vars <;> omega


section Rc
variable (m : Pattern s) {l0 k0 : ℕ}

lemma Rc_keep {l k : ℕ} (hk : k ≤ l) (hK : l0 < l ∨ (l = l0 ∧ k < k0)) :
    Rc m l0 k0 l k = gg m l k := by
  unfold Rc; rw [if_neg (by omega), if_pos hK]

lemma Rc_up {l k : ℕ} (hk : k ≤ l) (hK : ¬ (l0 < l ∨ (l = l0 ∧ k < k0))) :
    Rc m l0 k0 l k = Up m l0 k0 k := by
  unfold Rc; rw [if_neg (by omega), if_neg hK]

lemma Rc_h1 (C : PivCtx m l0 k0) (k : ℕ) : Rc m l0 k0 (n + 1) k = sN s k := by
  have := C.hl0
  by_cases hk : k ≤ n + 1
  · rw [Rc_keep m hk (by omega), gg_top]
  · unfold Rc; rw [if_pos (by omega)]; simp [sN]; omega

lemma Rc_h2 (l k : ℕ) (h : l < k) : Rc m l0 k0 l k = 0 := by
  unfold Rc; rw [if_pos h]

lemma Rc_h4 (C : PivCtx m l0 k0) (l k : ℕ) (h : ¬ (l < n + 2 ∧ k < n + 2)) :
    Rc m l0 k0 l k = 0 := by
  have := C.hl0
  by_cases hlk : l < k
  · exact Rc_h2 m l k hlk
  · have hl : n + 2 ≤ l := by omega
    rw [Rc_keep m (by omega) (by omega), gg_big m (by omega)]

lemma Rc_h5 (l k : ℕ) : Rc m l0 k0 l k ≤ sN s 0 := by
  unfold Rc Up
  split_ifs <;> first | omega | exact gg_le_sN0 m _ _ | exact (Nat.sub_le _ _).trans (gg_le_sN0 m _ _)

lemma Rc_h3 (C : PivCtx m l0 k0) (l k : ℕ) (hl : l + 1 < n + 2) (hk : k ≤ l) :
    Rc m l0 k0 l k ≤ Rc m l0 k0 (l + 1) k ∧ Rc m l0 k0 (l + 1) (k + 1) ≤ Rc m l0 k0 l k := by
  have hl0 := C.hl0
  have hk0 := C.hk0
  have hpiv := C.hpiv
  by_cases hK : l0 < l ∨ (l = l0 ∧ k < k0)
  · rw [Rc_keep m hk hK, Rc_keep m (l := l + 1) (k := k) (by omega) (by omega),
      Rc_keep m (l := l + 1) (k := k + 1) (by omega) (by omega)]
    exact gg_betw m hl hk
  · rw [Rc_up m hk hK]
    have hanti := Up_anti m C k
    constructor
    · by_cases hK1 : l0 < l + 1 ∨ (l + 1 = l0 ∧ k < k0)
      · rw [Rc_keep m (l := l + 1) (k := k) (by omega) hK1]
        rcases hK1 with h1 | ⟨h1, h2⟩
        · have hll : l = l0 := by omega
          subst hll
          have hb := gg_betw m (l := l) (k := k0) hl hk0
          unfold Up
          split_ifs with h3 h4
          · omega
          · subst h4; omega
          · exact le_rfl
        · subst h1
          unfold Up
          rw [if_pos h2]
      · rw [Rc_up m (l := l + 1) (k := k) (by omega) hK1]
    · by_cases hK1 : l0 < l + 1 ∨ (l + 1 = l0 ∧ k + 1 < k0)
      · rw [Rc_keep m (l := l + 1) (k := k + 1) (by omega) hK1]
        rcases hK1 with h1 | ⟨h1, h2⟩
        · have hll : l = l0 := by omega
          subst hll
          have h5 := gg_row_anti m (l + 1) k
          unfold Up
          split_ifs with h3 h4
          · omega
          · subst h4; omega
          · exact h5
        · subst h1
          have h5 := gg_row_anti m (l + 1) k
          unfold Up
          rw [if_pos (by omega)]
          exact h5
      · rw [Rc_up m (l := l + 1) (k := k + 1) (by omega) hK1]
        exact hanti

end Rc


lemma reset_eq (m : Pattern s) (q : Fin (n + 2) × Fin (n + 2))
    (C : PivCtx m q.1.val q.2.val) :
    ∀ t, t ≤ n + 1 → ∀ k, predecessorReset m q t k = Rc m q.1.val q.2.val (n + 1 - t) k := by
  have hl0 := C.hl0
  intro t
  induction t with
  | zero =>
    intro _ k
    rw [predecessorReset]
    by_cases hk : k ≤ n + 1
    · rw [Rc_keep m (by omega) (by omega)]; rfl
    · rw [Rc_h2 m _ _ (by omega)]
      exact gg_big m (by omega)
  | succ t ih =>
    intro ht k
    rw [predecessorReset]
    have e : n + 1 - t = (n + 1 - (t + 1)) + 1 := by omega
    rw [ih (by omega) k, e]
    generalize n + 1 - (t + 1) = L at *
    by_cases h0 : L < k
    · rw [if_pos h0, Rc_h2 m _ _ h0]
    · rw [if_neg h0]
      by_cases hK : q.1.val < L ∨ (L = q.1.val ∧ k < q.2.val)
      · rw [if_pos hK, Rc_keep m (by omega) hK]; rfl
      · rw [if_neg hK]
        by_cases hd : L = q.1.val ∧ k = q.2.val
        · rw [if_pos hd, Rc_up m (by omega) hK]
          unfold Up
          obtain ⟨h1, h2⟩ := hd
          rw [if_neg (by omega), if_pos h2, h1, h2]; rfl
        · rw [if_neg hd, Rc_up m (by omega) hK]
          by_cases hK1 : q.1.val < L + 1 ∨ (L + 1 = q.1.val ∧ k < q.2.val)
          · rw [Rc_keep m (by omega) hK1]
            unfold Up
            rcases hK1 with h1 | ⟨h1, h2⟩
            · have hLL : L = q.1.val := by omega
              rw [if_neg (by omega), if_neg (by omega), hLL]
            · rw [if_pos h2, h1]
          · rw [Rc_up m (by omega) hK1]


lemma positionLt_trans {p q r : Fin (n + 2) × Fin (n + 2)} (h1 : positionLt p q)
    (h2 : positionLt q r) : positionLt p r := by
  simp only [positionLt, Fin.lt_def, Fin.ext_iff] at *; omega

lemma positionLt_trichotomy (p q : Fin (n + 2) × Fin (n + 2)) :
    positionLt p q ∨ p = q ∨ positionLt q p := by
  rcases p with ⟨p1, p2⟩; rcases q with ⟨q1, q2⟩
  simp only [positionLt, Fin.lt_def, Prod.mk.injEq, Fin.ext_iff]; omega

lemma patternLt_gg {a b : Pattern s} : patternLt a b ↔ ∃ p : Fin (n + 2) × Fin (n + 2), p.2 ≤ p.1 ∧
    (∀ q : Fin (n + 2) × Fin (n + 2), q.2 ≤ q.1 → positionLt q p →
      gg a q.1.val q.2.val = gg b q.1.val q.2.val) ∧ gg a p.1.val p.2.val < gg b p.1.val p.2.val := by
  simp only [patternLt, pg_eq]

lemma Rc_copy (m : Pattern s) {l0 k0 : ℕ} {l k : ℕ} (hk : k ≤ l)
    (h : l < l0 ∨ (l = l0 ∧ k0 < k)) :
    Rc m l0 k0 l k = Rc m l0 k0 (l + 1) k := by
  rw [Rc_up m hk (by omega)]
  by_cases hK1 : l0 < l + 1 ∨ (l + 1 = l0 ∧ k < k0)
  · rw [Rc_keep m (by omega) hK1]
    unfold Up
    rcases hK1 with h1 | ⟨h1, h2⟩
    · have hLL : l = l0 := by omega
      rw [if_neg (by omega), if_neg (by omega), hLL]
    · rw [if_pos h2, h1]
  · rw [Rc_up m (by omega) hK1]

lemma pred_core (m : Pattern s) (q : Fin (n + 2) × Fin (n + 2))
    (hq : predecessorPivot m = some q) :
    ∃ P : Pattern s, (∀ l k : Fin (n + 2), patternGrid P l k = predecessorReset m q (n + 1 - l.val) k.val) ∧
      patternLt P m ∧ ∀ x : Pattern s, patternLt x m → x = P ∨ patternLt x P := by
  obtain ⟨hPP, hqq, hlater⟩ := pivot_some m q hq
  have C : PivCtx m q.1.val q.2.val := by
    refine ⟨by have := hPP.1; omega, hqq, hPP.2, ?_⟩
    intro l k hk hl hlk
    have := hlater (⟨l, by omega⟩, ⟨k, by omega⟩) hk (by
      simp only [positionLt, Fin.lt_def, Fin.ext_iff]; omega)
    simp only [PP, not_and, not_lt] at this
    exact this (by show l < n + 1; omega)
  have hl0 := C.hl0
  let P : Pattern s := mkPat s (Rc m q.1.val q.2.val) (Rc_h1 m C) (Rc_h2 m) (Rc_h3 m C) (Rc_h5 m)
  have hgP : ∀ l k, gg P l k = Rc m q.1.val q.2.val l k :=
    gg_mkPat s _ (Rc_h1 m C) (Rc_h2 m) (Rc_h3 m C) (Rc_h4 m C) (Rc_h5 m)
  have hPm : ∀ r : Fin (n + 2) × Fin (n + 2), r.2 ≤ r.1 → positionLt r q →
      gg P r.1.val r.2.val = gg m r.1.val r.2.val := by
    intro r hr hrq
    rw [hgP, Rc_keep m (l := r.1.val) (k := r.2.val) hr (by
      simp only [positionLt, Fin.lt_def, Fin.ext_iff] at hrq; omega)]
  have hPq : gg P q.1.val q.2.val = gg m q.1.val q.2.val - 1 := by
    rw [hgP, Rc_up m hqq (by omega)]
    unfold Up
    rw [if_neg (by omega), if_pos rfl]
  have hPlt : patternLt P m := by
    rw [patternLt_gg]
    refine ⟨q, hqq, fun r hr hrq => hPm r hr hrq, ?_⟩
    rw [hPq]
    have := hPP.2
    omega
  refine ⟨P, ?_, hPlt, ?_⟩
  · intro l k
    rw [pg_eq, hgP, reset_eq m q C (n + 1 - l.val) (by omega) k.val]
    have : n + 1 - (n + 1 - l.val) = l.val := by have := l.isLt; omega
    rw [this]
  · intro x hx
    rw [patternLt_gg] at hx
    obtain ⟨r, hr, hbef, hlt⟩ := hx
    have hr' : r.2.val ≤ r.1.val := hr
    have hnot : ¬ positionLt q r := by
      intro hqr
      have hqr' : r.1.val < q.1.val ∨ (q.1.val = r.1.val ∧ q.2.val < r.2.val) := by
        simp only [positionLt, Fin.lt_def, Fin.ext_iff] at hqr; omega
      have hrn : r.1.val ≤ n := by omega
      have h1 := C.hafter r.1.val r.2.val hr' hrn (by omega)
      have h2 := hbef (⟨r.1.val + 1, by omega⟩, ⟨r.2.val + 1, by omega⟩)
        (by show r.2.val + 1 ≤ r.1.val + 1; omega)
        (by simp only [positionLt, Fin.lt_def]; omega)
      have h3 := (gg_betw x (l := r.1.val) (k := r.2.val) (by omega) hr').2
      simp only [] at h2
      omega
    rcases positionLt_trichotomy r q with h | h | h
    · right
      rw [patternLt_gg]
      refine ⟨r, hr, ?_, ?_⟩
      · intro q' hq' hq'r
        rw [hbef q' hq' hq'r]; exact (hPm q' hq' (positionLt_trans hq'r h)).symm
      · rw [hPm r hr h]; exact hlt
    · rw [h] at hbef hlt
      have hlt' : gg x q.1.val q.2.val < gg m q.1.val q.2.val := hlt
      by_cases heq : gg x q.1.val q.2.val = gg P q.1.val q.2.val
      · by_cases hxP : x = P
        · left; exact hxP
        · right
          rcases plt_trich x P with h1 | h1 | h1
          · exact h1
          · exact absurd h1 hxP
          · exfalso
            rw [patternLt_gg] at h1
            obtain ⟨r2, hr2, hbef2, hlt2⟩ := h1
            have hr2' : r2.2.val ≤ r2.1.val := hr2
            rcases positionLt_trichotomy r2 q with h3 | h3 | h3
            · have := hbef r2 hr2 h3
              rw [hPm r2 hr2 h3] at hlt2
              omega
            · rw [h3] at hlt2
              omega
            · have h3' : r2.1.val < q.1.val ∨ (q.1.val = r2.1.val ∧ q.2.val < r2.2.val) := by
                simp only [positionLt, Fin.lt_def, Fin.ext_iff] at h3; omega
              have hrn : r2.1.val ≤ n := by omega
              have h4 := hbef2 (⟨r2.1.val + 1, by omega⟩, ⟨r2.2.val, by omega⟩)
                (by show r2.2.val ≤ r2.1.val + 1; omega)
                (by simp only [positionLt, Fin.lt_def]; omega)
              have h5 := (gg_betw x (l := r2.1.val) (k := r2.2.val) (by omega) hr2').1
              have h6 : gg P r2.1.val r2.2.val = gg P (r2.1.val + 1) r2.2.val := by
                rw [hgP, hgP]
                exact Rc_copy m hr2' (by omega)
              simp only [] at h4
              omega
      · right
        rw [patternLt_gg]
        refine ⟨q, hqq, ?_, ?_⟩
        · intro q' hq' hq'r
          rw [hbef q' hq' hq'r]; exact (hPm q' hq' hq'r).symm
        · omega
    · exact absurd h hnot


lemma sN_eq (s : GTTopRow n) {j : ℕ} (h : j < n + 2) : sN s j = s.val ⟨j, h⟩ := by
  simp [sN, h]

lemma min_iff (m : Pattern s) : m = Pmin s ↔ ∀ (l k : Fin (n + 2)) (hkl : k ≤ l),
    patternGrid m l k = s.val ⟨k.val + (n + 1 - l.val), by
      have hl := l.isLt
      have hklNat : k.val ≤ l.val := hkl
      omega⟩ := by
  constructor
  · rintro rfl l k hkl
    have hl := l.isLt
    have hklNat : k.val ≤ l.val := hkl
    rw [pg_eq, gg_Pmin, G0, if_pos ⟨hklNat, by omega⟩, sN_eq s (by omega)]
  · intro h
    apply gg_ext
    intro l k
    rw [gg_Pmin, G0]
    split_ifs with hh
    · rw [gg_in m (by omega) (by omega), sN_eq s (by omega)]
      exact h ⟨l, by omega⟩ ⟨k, by omega⟩ hh.1
    · by_cases hl : l ≤ n + 1
      · rw [gg_zero m (by omega)]
      · rw [gg_big m (by omega)]

lemma top_iff (m : Pattern s) : m = Ptop s ↔ ∀ l k : Fin (n + 2), k ≤ l →
    patternGrid m l k = s.val k := by
  constructor
  · rintro rfl l k hkl
    have hl := l.isLt
    have hklNat : k.val ≤ l.val := hkl
    rw [pg_eq, gg_Ptop, GT, if_pos ⟨hklNat, by omega⟩, sN_eq s k.isLt]
  · intro h
    apply gg_ext
    intro l k
    rw [gg_Ptop, GT]
    split_ifs with hh
    · rw [gg_in m (by omega) (by omega), sN_eq s (by omega)]
      exact h ⟨l, by omega⟩ ⟨k, by omega⟩ hh.1
    · by_cases hl : l ≤ n + 1
      · rw [gg_zero m (by omega)]
      · rw [gg_big m (by omega)]

lemma pred_spec (m : Pattern s) :
    (patternPredecessor m = none → patternRank m = 1) ∧
    (∀ raw, patternPredecessor m = some raw → ∃ p : Pattern s, patternGrid p = raw ∧
        patternRank m = patternRank p + 1 ∧
        ∀ q : Pattern s, patternLt q m → q = p ∨ patternLt q p) := by
  constructor
  · intro h
    unfold patternPredecessor at h
    rw [Option.map_eq_none_iff] at h
    rw [rank_eq_one_iff]
    exact none_min m (pivot_none m h)
  · intro raw h
    unfold patternPredecessor at h
    rw [Option.map_eq_some_iff] at h
    obtain ⟨q, hq, hraw⟩ := h
    obtain ⟨P, hP1, hPlt, himm⟩ := pred_core m q hq
    refine ⟨P, ?_, ?_, himm⟩
    · rw [← hraw]
      funext l k
      exact hP1 l k
    · unfold patternRank
      have : (Finset.univ.filter fun x : Pattern s => patternLt x m) =
          insert P (Finset.univ.filter fun x : Pattern s => patternLt x P) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · intro hx
          rcases himm x hx with h | h
          · left; exact h
          · right; exact h
        · rintro (rfl | h)
          · exact hPlt
          · exact plt_trans h hPlt
      rw [this, Finset.card_insert_of_notMem (by simp [plt_irrefl])]
      omega

lemma chain_exists : ∀ N, ∀ m : Pattern s, patternRank m = N + 1 → HasPredecessorChain N m := by
  intro N
  induction N with
  | zero =>
    intro m hm
    show patternPredecessor m = none
    by_contra hne
    obtain ⟨raw, hraw⟩ := Option.ne_none_iff_exists'.mp hne
    obtain ⟨p, _, hr, _⟩ := (pred_spec m).2 raw hraw
    have := rank_pos p
    omega
  | succ N ih =>
    intro m hm
    cases hpm : patternPredecessor m with
    | none =>
      have := (pred_spec m).1 hpm
      omega
    | some raw =>
      obtain ⟨p, hp1, hr, _⟩ := (pred_spec m).2 raw hpm
      refine ⟨p, ?_, ih p (by omega)⟩
      rw [hpm, hp1]

lemma chain_unique : ∀ N, ∀ m : Pattern s, HasPredecessorChain N m → N + 1 = patternRank m := by
  intro N
  induction N with
  | zero =>
    intro m hm
    exact ((pred_spec m).1 hm).symm
  | succ N ih =>
    intro m ⟨p, hp, hc⟩
    obtain ⟨p', hp1, hr, _⟩ := (pred_spec m).2 _ hp
    have : p' = p := gg_ext (fun l k => by
      by_cases hh : l < n + 2 ∧ k < n + 2
      · have := congrFun (congrFun hp1 ⟨l, hh.1⟩) ⟨k, hh.2⟩
        rw [pg_eq, pg_eq] at this
        exact this
      · rw [gg_big _ hh, gg_big _ hh])
    subst this
    have := ih p' hc
    omega


end GTAux

end QAlgorithms.Papers.Independent.Renew46.P15

open QAlgorithms.Papers.Independent.Renew46.P15

attribute [local instance] Classical.propDecidable

theorem solution {n : ℕ} (s : GTTopRow n) :
    0 < Fintype.card (Pattern s) ∧
    Function.Injective (patternRank (s := s)) ∧
    (∀ q : ℕ, (∃ m : Pattern s, patternRank m = q) ↔
      1 ≤ q ∧ q ≤ Fintype.card (Pattern s)) ∧
    (∀ a b : Pattern s, patternLt a b ↔ patternRank a < patternRank b) ∧
    (∀ m : Pattern s,
      (patternRank m = 1 ↔ ∀ (l k : Fin (n + 2)) (hkl : k ≤ l),
        patternGrid m l k = s.val ⟨k.val + (n + 1 - l.val), by
          have hl := l.isLt
          have hklNat : k.val ≤ l.val := hkl
          omega⟩) ∧
      (patternRank m = Fintype.card (Pattern s) ↔
        ∀ l k : Fin (n + 2), k ≤ l → patternGrid m l k = s.val k) ∧
      (match patternPredecessor m with
        | none => patternRank m = 1
        | some raw => ∃ p : Pattern s, patternGrid p = raw ∧
            patternRank m = patternRank p + 1 ∧
            ∀ q : Pattern s, patternLt q m → q = p ∨ patternLt q p) ∧
      HasPredecessorChain (patternRank m - 1) m ∧
      ∀ steps, HasPredecessorChain steps m → steps + 1 = patternRank m) := by
  refine ⟨Fintype.card_pos_iff.mpr ⟨Ptop s⟩, rank_inj, ?_, rank_lt_iff, ?_⟩
  · intro q
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨rank_pos m, rank_le_card m⟩
    · rintro ⟨h1, h2⟩
      exact rank_surj q h1 h2
  · intro m
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [rank_eq_one_iff]; exact min_iff m
    · rw [rank_eq_card_iff]; exact top_iff m
    · cases hpm : patternPredecessor m with
      | none => exact (pred_spec m).1 hpm
      | some raw => exact (pred_spec m).2 raw hpm
    · exact chain_exists _ m (by have := rank_pos m; omega)
    · intro steps h
      exact chain_unique steps m h

end
