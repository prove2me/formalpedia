-- Prove2me | solution 1 for OnlineColoringKYY.Supplement.theorem_5_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T15:32:48.476114+00:00
-- url     : https://prove2.me/submissions/87c9706b-b291-43c3-953f-17c81d11ef13

import Mathlib
import Definitions.Def_OnlineColoringKYY_prefixGraph
import Definitions.Def_OnlineColoringKYY_Supplement_Common
import Definitions.Def_OnlineColoringKYY_Supplement_threeLevel

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T55
open Classical OnlineColoringKYY.Supplement
/-!
Blueprint for Theorem 5.5 (three-level algorithm), q414.
Every lemma below is a stub (`sorry`) proved in a Part file; `chk_theorem_5_5` is proved from them.

Notation. A coloring is `c : List ℕ` (colors of vertices `0, …, len − 1` in arrival order).
`lvl c j` = number of colors used exactly `j` times. `pairs c` = the pairs `(a, b)`, `a < b`, the two
vertices of a level-2 color. `Last G φ B a` = the vertices `b ∈ B` non-adjacent to `a` such that every
later `b' ∈ B` of the same base color `φ` is adjacent to `a` (paper's Lemma 5.3).
-/
/-- The trajectory condition: each entry of `c` is in the support of the step distribution given the
prefix before it. -/
def Traj (θ : ℕ) (sel : List ℕ → Finset ℕ → ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) (c : List ℕ) :
    Prop :=
  c.length ≤ n ∧ ∀ u (hn : u < n), u < c.length →
    c.getD u 0 ∈ (threeLevelStep θ sel G ⟨u, hn⟩ (c.take u)).support

/-- Number of colors used exactly `j` times in `c`. -/
noncomputable def lvl (c : List ℕ) (j : ℕ) : ℕ := (c.toFinset.filter (fun x => c.count x = j)).card

/-- Adjacency of vertices given by their natural-number indices. -/
def adjN {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℕ) : Prop :=
  ∃ (ha : a < n) (hb : b < n), G.Adj ⟨a, ha⟩ ⟨b, hb⟩

/-- The pairs `(a, b)` with `a < b` that are the two vertices of a level-2 color of `c`. -/
noncomputable def pairs (c : List ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range c.length) ×ˢ (Finset.range c.length)).filter
    (fun p => p.1 < p.2 ∧ c.getD p.1 0 = c.getD p.2 0 ∧ c.count (c.getD p.1 0) = 2)

/-- Paper's Lemma 5.3 candidate set for `a` inside `B`. -/
noncomputable def Last {n : ℕ} (G : SimpleGraph (Fin n)) (φ : ℕ → ℕ) (B : Finset ℕ) (a : ℕ) :
    Finset ℕ :=
  B.filter (fun b => ¬ adjN G a b ∧ ∀ b' ∈ B, b < b' → φ b' = φ b → adjN G a b')

/-- The event that each pair `(a, b) ∈ P` is realized: `a < b`, and if `b` has arrived then at its
arrival the color of `a` was used exactly once, and `b` took the color of `a`. -/
def Ev (P : Finset (ℕ × ℕ)) (c : List ℕ) : Prop :=
  ∀ p ∈ P, p.1 < p.2 ∧ (p.2 < c.length →
    (c.take p.2).count (c.getD p.1 0) = 1 ∧ c.getD p.2 0 = c.getD p.1 0)

/-- The pairing built from `A` and a choice `f a ∈ Last … a` for each `a ∈ A`. -/
noncomputable def pairOf (A : Finset ℕ) (f : (a : ℕ) → a ∈ A → ℕ) : Finset (ℕ × ℕ) :=
  A.attach.image (fun a => (a.1, f a.1 a.2))

/-- The base coloring on indices, from a `k`-coloring of `G`. -/
def phiN {n k : ℕ} {G : SimpleGraph (Fin n)} (C : G.Coloring (Fin k)) (a : ℕ) : ℕ :=
  if h : a < n then (C ⟨a, h⟩).val else 0

end OnlineColoringKYY.Supplement.Dev.T55
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T55.PartA
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T55
/-! ### Basic list facts -/
lemma lt_freshColor (c : List ℕ) (x : ℕ) (hx : x ∈ c) : x < freshColor c := by
  induction c with
  | nil => simp at hx
  | cons a l ih =>
    simp only [freshColor, List.foldr_cons] at *
    rcases List.mem_cons.mp hx with rfl | h
    · exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
    · exact lt_of_lt_of_le (ih h) (le_max_right _ _)

lemma freshColor_not_mem (c : List ℕ) : freshColor c ∉ c := fun h =>
  lt_irrefl _ (lt_freshColor c _ h)

lemma getD_take_of_lt (c : List ℕ) (j i : ℕ) (h : i < j) :
    (c.take j).getD i 0 = c.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, h]

lemma getD_mem_take (c : List ℕ) (j u : ℕ) (h : u < j) (hu : u < c.length) :
    c.getD u 0 ∈ c.take j := by
  rw [← getD_take_of_lt c j u h, List.getD_eq_getElem _ _ (by simp; omega)]
  exact List.getElem_mem _

lemma getD_mem (c : List ℕ) (u : ℕ) (hu : u < c.length) : c.getD u 0 ∈ c := by
  rw [List.getD_eq_getElem _ _ hu]
  exact List.getElem_mem _

/-- Count as the number of positions. -/
lemma count_eq_card_pos (c : List ℕ) (x : ℕ) :
    c.count x = ((Finset.range c.length).filter (fun i => c.getD i 0 = x)).card := by
  induction c using List.reverseRecOn with
  | nil => simp
  | append_singleton l a ih =>
    rw [List.count_append, ih, List.length_append, List.length_singleton,
      Finset.range_add_one, Finset.filter_insert]
    have hfl : (Finset.range l.length).filter (fun i => (l ++ [a]).getD i 0 = x) =
        (Finset.range l.length).filter (fun i => l.getD i 0 = x) := by
      apply Finset.filter_congr
      intro i hi
      rw [List.getD_append _ _ _ _ (Finset.mem_range.mp hi)]
    have hl : (l ++ [a]).getD l.length 0 = a := by
      rw [List.getD_append_right _ _ _ _ le_rfl]; simp
    rw [hfl, hl]
    by_cases hax : a = x
    · subst hax
      rw [if_pos rfl, Finset.card_insert_of_notMem (by simp)]
      simp
    · rw [if_neg hax]
      simpa [List.count_singleton] using hax

lemma count_take_eq (c : List ℕ) (j x : ℕ) :
    (c.take j).count x =
      ((Finset.range c.length).filter (fun i => i < j ∧ c.getD i 0 = x)).card := by
  rw [count_eq_card_pos]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, List.length_take]
  constructor
  · rintro ⟨h1, h2⟩
    have hij : i < j := lt_of_lt_of_le h1 (min_le_left _ _)
    exact ⟨lt_of_lt_of_le h1 (min_le_right _ _), hij, by rwa [getD_take_of_lt c j i hij] at h2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨lt_min h2 h1, by rw [getD_take_of_lt c j i h2]; exact h3⟩

/-! ### Support of one step -/
lemma step_cases (θ : ℕ) (sel : List ℕ → Finset ℕ → ℕ)
    (hsel : ∀ c S, S.Nonempty → sel c S ∈ S) {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    (c' : List ℕ) (x : ℕ) (hx : x ∈ (threeLevelStep θ sel G v c').support) :
    (x ∈ c' ∧ (c'.count x = 1 ∨ c'.count x = 2) ∧ Eligible G v c' x ∧
        ((eligibleLevel G v c' 2).Nonempty → c'.count x = 2)) ∨
      (x ∉ c' ∧ ¬ (eligibleLevel G v c' 2).Nonempty ∧
        ¬ ((eligibleLevel G v c' 1).Nonempty ∧ θ ≤ (eligibleLevel G v c' 1).card)) := by
  unfold threeLevelStep at hx
  split_ifs at hx with h2 h1
  · rw [PMF.support_pure, Set.mem_singleton_iff] at hx
    have hm := hsel c' _ h2
    rw [← hx] at hm
    simp only [eligibleLevel, Finset.mem_filter, List.mem_toFinset] at hm
    exact Or.inl ⟨hm.1, Or.inr hm.2.1, hm.2.2, fun _ => hm.2.1⟩
  · rw [PMF.mem_support_uniformOfFinset_iff] at hx
    simp only [eligibleLevel, Finset.mem_filter, List.mem_toFinset] at hx
    exact Or.inl ⟨hx.1, Or.inl hx.2.1, hx.2.2, fun h => absurd h h2⟩
  · rw [PMF.support_pure, Set.mem_singleton_iff] at hx
    subst hx
    exact Or.inr ⟨freshColor_not_mem c', h2, h1⟩

/-! ### Trajectory helpers -/
lemma traj_cases {θ : ℕ} {sel : List ℕ → Finset ℕ → ℕ}
    (hsel : ∀ c S, S.Nonempty → sel c S ∈ S) {n : ℕ} {G : SimpleGraph (Fin n)} {c : List ℕ}
    (hc : Traj θ sel G c) (u : ℕ) (hu : u < c.length) :
    (c.getD u 0 ∈ c.take u ∧ ((c.take u).count (c.getD u 0) = 1 ∨
        (c.take u).count (c.getD u 0) = 2) ∧
        Eligible G ⟨u, lt_of_lt_of_le hu hc.1⟩ (c.take u) (c.getD u 0) ∧
        ((eligibleLevel G ⟨u, lt_of_lt_of_le hu hc.1⟩ (c.take u) 2).Nonempty →
          (c.take u).count (c.getD u 0) = 2)) ∨
      (c.getD u 0 ∉ c.take u ∧
        ¬ (eligibleLevel G ⟨u, lt_of_lt_of_le hu hc.1⟩ (c.take u) 2).Nonempty ∧
        ¬ ((eligibleLevel G ⟨u, lt_of_lt_of_le hu hc.1⟩ (c.take u) 1).Nonempty ∧
          θ ≤ (eligibleLevel G ⟨u, lt_of_lt_of_le hu hc.1⟩ (c.take u) 1).card)) :=
  step_cases θ sel hsel G _ _ _ (hc.2 u _ hu)

lemma prefix_count_le_two {θ : ℕ} {sel : List ℕ → Finset ℕ → ℕ}
    (hsel : ∀ c S, S.Nonempty → sel c S ∈ S) {n : ℕ} {G : SimpleGraph (Fin n)} {c : List ℕ}
    (hc : Traj θ sel G c) (u : ℕ) (hu : u < c.length) :
    (c.take u).count (c.getD u 0) ≤ 2 := by
  rcases traj_cases hsel hc u hu with h | h
  · omega
  · rw [List.count_eq_zero_of_not_mem h.1]; omega

theorem count_le_three (θ : ℕ) (sel : List ℕ → Finset ℕ → ℕ)
    (hsel : ∀ c S, S.Nonempty → sel c S ∈ S) {n : ℕ} (G : SimpleGraph (Fin n)) (c : List ℕ)
    (hc : Traj θ sel G c) (x : ℕ) : c.count x ≤ 3 := by
  have key : ∀ j, (c.take j).count x ≤ 3 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      by_cases hj : j < c.length
      · rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.count_append,
          List.count_singleton]
        have h2 := prefix_count_le_two hsel hc j hj
        rw [List.getD_eq_getElem _ _ hj] at h2
        split_ifs with hx
        · have hx' := beq_iff_eq.mp hx
          subst hx'
          omega
        · omega
      · rw [List.take_of_length_le (by omega)]
        rw [List.take_of_length_le (by omega)] at ih
        exact ih
  simpa using key c.length

end OnlineColoringKYY.Supplement.Dev.T55.PartA
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T55
open Classical OnlineColoringKYY.Supplement
alias count_le_three := OnlineColoringKYY.Supplement.Dev.T55.PartA.count_le_three

end OnlineColoringKYY.Supplement.Dev.T55
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T55.PartA
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T55
/-! ### Positions of a level-2 color -/
lemma mem_of_card_two (S : Finset ℕ) (hS : S.card = 2) (a b : ℕ) (ha : a ∈ S) (hb : b ∈ S)
    (hab : a < b) : ∀ u ∈ S, u = a ∨ u = b := by
  obtain ⟨s, t, hst, rfl⟩ := Finset.card_eq_two.mp hS
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb ⊢
  intro u hu
  omega

lemma mem_pairs (c : List ℕ) (p : ℕ × ℕ) :
    p ∈ pairs c ↔ p.1 < c.length ∧ p.2 < c.length ∧ p.1 < p.2 ∧
      c.getD p.1 0 = c.getD p.2 0 ∧ c.count (c.getD p.1 0) = 2 := by
  simp only [pairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range, and_assoc]

lemma pair_pos (c : List ℕ) (p : ℕ × ℕ) (hp : p ∈ pairs c) (u : ℕ) (hu : u < c.length)
    (hux : c.getD u 0 = c.getD p.1 0) : u = p.1 ∨ u = p.2 := by
  rw [mem_pairs] at hp
  obtain ⟨h1, h2, h12, he, hcount⟩ := hp
  rw [count_eq_card_pos] at hcount
  exact mem_of_card_two _ hcount p.1 p.2 (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h1, rfl⟩)
    (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h2, he.symm⟩) h12 u
    (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hu, hux⟩)

lemma pair_eq (c : List ℕ) (p q : ℕ × ℕ) (hp : p ∈ pairs c) (hq : q ∈ pairs c)
    (h : c.getD q.1 0 = c.getD p.1 0) : p = q := by
  have hq' := (mem_pairs c q).mp hq
  have e1 := pair_pos c p hp q.1 hq'.1 h
  have e2 := pair_pos c p hp q.2 hq'.2.1 (by rw [← hq'.2.2.2.1, h])
  have := (mem_pairs c p).mp hp
  ext <;> omega

theorem card_pairs (c : List ℕ) : (pairs c).card = lvl c 2 := by
  unfold lvl
  apply Finset.card_bij (fun p _ => c.getD p.1 0)
  · intro p hp
    have h := (mem_pairs c p).mp hp
    simp only [Finset.mem_filter, List.mem_toFinset]
    exact ⟨getD_mem c _ h.1, h.2.2.2.2⟩
  · intro p hp q hq h
    exact pair_eq c p q hp hq h.symm
  · intro x hx
    simp only [Finset.mem_filter, List.mem_toFinset] at hx
    have hc2 := hx.2
    rw [count_eq_card_pos] at hc2
    obtain ⟨s, t, hst, hP⟩ := Finset.card_eq_two.mp hc2
    have hs : s ∈ (Finset.range c.length).filter (fun i => c.getD i 0 = x) := by
      rw [hP]; simp
    have ht : t ∈ (Finset.range c.length).filter (fun i => c.getD i 0 = x) := by
      rw [hP]; simp
    simp only [Finset.mem_filter, Finset.mem_range] at hs ht
    rcases lt_or_gt_of_ne hst with h | h
    · refine ⟨(s, t), ?_, hs.2⟩
      rw [mem_pairs]
      exact ⟨hs.1, ht.1, h, by rw [hs.2, ht.2], by rw [hs.2]; exact hx.2⟩
    · refine ⟨(t, s), ?_, ht.2⟩
      rw [mem_pairs]
      exact ⟨ht.1, hs.1, h, by rw [hs.2, ht.2], by rw [ht.2]; exact hx.2⟩

/-! ### Adjacency helpers -/
lemma prefixAdj_of_adjN {n : ℕ} (G : SimpleGraph (Fin n)) (u v : ℕ) (hv : v < n)
    (huv : u < v) (h : adjN G u v) : prefixAdj G ⟨v, hv⟩ u v := by
  obtain ⟨hu, hv', hadj⟩ := h
  exact ⟨by simp; omega, by simp, hadj⟩

lemma adjN_of_prefixAdj {n : ℕ} (G : SimpleGraph (Fin n)) (u v : ℕ) (hv : v < n)
    (h : prefixAdj G ⟨v, hv⟩ u v) : adjN G u v := by
  obtain ⟨hu, hv', hadj⟩ := h
  exact ⟨by simp at hu; omega, hv, hadj⟩

lemma phiN_ne_of_adjN {n k : ℕ} {G : SimpleGraph (Fin n)} (C : G.Coloring (Fin k)) (u v : ℕ)
    (h : adjN G u v) : phiN C u ≠ phiN C v := by
  obtain ⟨hu, hv, hadj⟩ := h
  unfold phiN
  rw [dif_pos hu, dif_pos hv]
  intro he
  exact C.valid hadj (Fin.ext he)

/-! ### run_support -/
theorem run_support (θ : ℕ) (sel : List ℕ → Finset ℕ → ℕ) {n : ℕ} (G : SimpleGraph (Fin n))
    (m : ℕ) (h : m ≤ n) (c : List ℕ) (hc : c ∈ (threeLevelRun θ sel G m h).support) :
    c.length = m ∧ Traj θ sel G c := by
  induction m generalizing c with
  | zero =>
    simp only [threeLevelRun, PMF.support_pure, Set.mem_singleton_iff] at hc
    subst hc
    exact ⟨rfl, Nat.zero_le _, fun u _ hu => absurd hu (by simp)⟩
  | succ m ih =>
    simp only [threeLevelRun, PMF.mem_support_bind_iff, PMF.support_map,
      Set.mem_image] at hc
    obtain ⟨c0, hc0, x, hx, rfl⟩ := hc
    obtain ⟨hlen, -, htr⟩ := ih (Nat.le_of_succ_le h) c0 hc0
    refine ⟨by simp [hlen], by simp [hlen]; omega, fun u hn hu => ?_⟩
    simp only [List.length_append, List.length_singleton] at hu
    rcases Nat.lt_succ_iff_lt_or_eq.mp (by omega : u < m + 1) with hum | rfl
    · rw [List.getD_append _ _ _ _ (by omega), List.take_append_of_le_length (by omega)]
      exact htr u hn (by omega)
    · subst hlen
      rw [List.getD_append_right _ _ _ _ le_rfl, List.take_left' rfl]
      simpa using hx

end OnlineColoringKYY.Supplement.Dev.T55.PartA
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T55
open Classical OnlineColoringKYY.Supplement
/-! ### Part A: support and deterministic facts -/
alias run_support := OnlineColoringKYY.Supplement.Dev.T55.PartA.run_support

end OnlineColoringKYY.Supplement.Dev.T55
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T55.PartA
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T55
/-! ### card_Last_le -/
theorem card_Last_le {n k : ℕ} (G : SimpleGraph (Fin n)) (C : G.Coloring (Fin k))
    (B : Finset ℕ) (a : ℕ) (hB : ∀ b ∈ B, b < n) : (Last G (phiN C) B a).card ≤ k := by
  have hk : (Finset.range k).card = k := Finset.card_range k
  conv_rhs => rw [← hk]
  apply Finset.card_le_card_of_injOn (phiN C)
  · intro b hb
    have hbB : b ∈ B := (Finset.mem_filter.mp hb).1
    simp only [Finset.coe_range, Set.mem_Iio, phiN, dif_pos (hB b hbB)]
    exact (C ⟨b, hB b hbB⟩).isLt
  · intro b1 hb1 b2 hb2 heq
    simp only [Finset.coe_filter, Last, Set.mem_ofPred_eq] at hb1 hb2
    rcases lt_trichotomy b1 b2 with h | h | h
    · exact absurd (hb1.2.2 b2 hb2.1 h heq.symm) hb2.2.1
    · exact h
    · exact absurd (hb2.2.2 b1 hb1.1 h heq) hb1.2.1

/-! ### card_toFinset_eq -/
theorem card_toFinset_eq (c : List ℕ) (h3 : ∀ x, c.count x ≤ 3) :
    3 * c.toFinset.card = c.length + 2 * lvl c 1 + lvl c 2 := by
  unfold lvl
  rw [Finset.card_filter, Finset.card_filter, ← List.sum_toFinset_count_eq_length,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    Finset.card_eq_sum_ones, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  have hpos : 0 < c.count x := List.count_pos_iff.mpr (List.mem_toFinset.mp hx)
  have := h3 x
  interval_cases (c.count x) <;> simp

end OnlineColoringKYY.Supplement.Dev.T55.PartA
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T55
open Classical OnlineColoringKYY.Supplement
alias card_toFinset_eq := OnlineColoringKYY.Supplement.Dev.T55.PartA.card_toFinset_eq

end OnlineColoringKYY.Supplement.Dev.T55
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T55.PartA
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T55
/-! ### lvl_one_le -/
lemma pos_unique (c : List ℕ) (x : ℕ) (hx : c.count x = 1) (u1 u2 : ℕ) (h1 : u1 < c.length)
    (h2 : u2 < c.length) (e1 : c.getD u1 0 = x) (e2 : c.getD u2 0 = x) : u1 = u2 := by
  rw [count_eq_card_pos] at hx
  exact Finset.card_le_one.mp hx.le u1 (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h1, e1⟩) u2
    (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h2, e2⟩)

lemma exists_pos_of_mem (c : List ℕ) (x : ℕ) (hx : x ∈ c) :
    ∃ u, u < c.length ∧ c.getD u 0 = x := by
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem hx
  exact ⟨i, hi, by rw [List.getD_eq_getElem _ _ hi, he]⟩

lemma fiber_le (θ : ℕ) (hθ : 1 ≤ θ) (sel : List ℕ → Finset ℕ → ℕ)
    (hsel : ∀ c S, S.Nonempty → sel c S ∈ S) {n k : ℕ} (G : SimpleGraph (Fin n))
    (C : G.Coloring (Fin k)) (c : List ℕ) (hc : Traj θ sel G c) (i : ℕ) :
    (((Finset.range c.length).filter (fun u => c.count (c.getD u 0) = 1)).filter
      (fun u => phiN C u = i)).card ≤ θ := by
  set F := ((Finset.range c.length).filter (fun u => c.count (c.getD u 0) = 1)).filter
      (fun u => phiN C u = i) with hF
  have memF : ∀ u, u ∈ F ↔ u < c.length ∧ c.count (c.getD u 0) = 1 ∧ phiN C u = i := by
    intro u; simp [hF, and_assoc]
  by_contra hlt
  rw [not_le] at hlt
  have hne : F.Nonempty := Finset.card_pos.mp (by omega)
  set w := F.max' hne with hw
  have hwF : w ∈ F := F.max'_mem hne
  obtain ⟨hwl, hwc, hwi⟩ := (memF w).mp hwF
  have hwn : w < n := lt_of_lt_of_le hwl hc.1
  set E1 := eligibleLevel G ⟨w, lt_of_lt_of_le hwl hc.1⟩ (c.take w) 1 with hE1
  -- the earlier members of `F` give `θ` eligible level-1 colors
  have hsub : (F.erase w).image (fun u => c.getD u 0) ⊆ E1 := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨huw, huF⟩ := Finset.mem_erase.mp hu
    obtain ⟨hul, huc, hui⟩ := (memF u).mp huF
    have hlt : u < w := lt_of_le_of_ne (F.le_max' u huF) huw
    have hmem := getD_mem_take c w u hlt hul
    simp only [hE1, eligibleLevel, Finset.mem_filter, List.mem_toFinset]
    refine ⟨hmem, ?_, ?_⟩
    · have h1 := (List.take_sublist w c).count_le (c.getD u 0)
      have h2 := List.count_pos_iff.mpr hmem
      omega
    · intro u' hu' hadj he
      rw [getD_take_of_lt c w u' hu'] at he
      have hu'w : u' < w := hu'
      have hu'l : u' < c.length := by omega
      have := pos_unique c _ huc u' u hu'l hul he rfl
      subst this
      exact phiN_ne_of_adjN C u' w (adjN_of_prefixAdj G u' w hwn hadj) (by rw [hui, hwi])
  have hinj : Set.InjOn (fun u => c.getD u 0) (F.erase w : Set ℕ) := by
    intro u1 h1 u2 h2 he
    obtain ⟨h1l, h1c, -⟩ := (memF u1).mp (Finset.mem_of_mem_erase h1)
    obtain ⟨h2l, -, -⟩ := (memF u2).mp (Finset.mem_of_mem_erase h2)
    exact pos_unique c _ h1c u1 u2 h1l h2l rfl he.symm
  have hcardE : θ ≤ E1.card := by
    have := Finset.card_le_card hsub
    rw [Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem hwF] at this
    omega
  -- but `w` received a fresh color
  rcases traj_cases hsel hc w hwl with h | h
  · obtain ⟨u, hu, hue⟩ := exists_pos_of_mem _ _ h.1
    rw [List.length_take] at hu
    have hu' : u < w := lt_of_lt_of_le hu (min_le_left _ _)
    rw [getD_take_of_lt c w u hu'] at hue
    have := pos_unique c _ hwc u w (by omega) hwl hue rfl
    omega
  · exact h.2.2 ⟨Finset.card_pos.mp (lt_of_lt_of_le hθ hcardE), hcardE⟩

/-- Paper's Lemma 5.1. -/
theorem lvl_one_le (θ : ℕ) (hθ : 1 ≤ θ) (sel : List ℕ → Finset ℕ → ℕ)
    (hsel : ∀ c S, S.Nonempty → sel c S ∈ S) {n k : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.Colorable k) (c : List ℕ) (hc : Traj θ sel G c) : lvl c 1 ≤ k * θ := by
  obtain ⟨C⟩ := hG
  set V1 := (Finset.range c.length).filter (fun u => c.count (c.getD u 0) = 1) with hV1
  have h1 : lvl c 1 ≤ V1.card := by
    unfold lvl
    refine (Finset.card_le_card ?_).trans (Finset.card_image_le (f := fun u => c.getD u 0))
    intro x hx
    simp only [Finset.mem_filter, List.mem_toFinset] at hx
    obtain ⟨u, hu, rfl⟩ := exists_pos_of_mem c x hx.1
    exact Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hu, hx.2⟩, rfl⟩
  have h2 : V1.card = ∑ i ∈ Finset.range k, (V1.filter (fun u => phiN C u = i)).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro u hu
    have hu' : u < c.length := by simp [hV1] at hu; exact hu.1
    have hun : u < n := lt_of_lt_of_le hu' hc.1
    simp only [Finset.coe_range, Set.mem_Iio, phiN, dif_pos hun]
    exact (C ⟨u, hun⟩).isLt
  have h3 : ∑ i ∈ Finset.range k, (V1.filter (fun u => phiN C u = i)).card ≤
      ∑ _i ∈ Finset.range k, θ :=
    Finset.sum_le_sum (fun i _ => fiber_le θ hθ sel hsel G C c hc i)
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at h3
  omega

end OnlineColoringKYY.Supplement.Dev.T55.PartA
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T55
open Classical OnlineColoringKYY.Supplement
alias lvl_one_le := OnlineColoringKYY.Supplement.Dev.T55.PartA.lvl_one_le

alias card_Last_le := OnlineColoringKYY.Supplement.Dev.T55.PartA.card_Last_le

alias card_pairs := OnlineColoringKYY.Supplement.Dev.T55.PartA.card_pairs

end OnlineColoringKYY.Supplement.Dev.T55
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T55.PartA
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T55
/-! ### pairs_structure -/
theorem pairs_structure (θ : ℕ) (sel : List ℕ → Finset ℕ → ℕ)
    (hsel : ∀ c S, S.Nonempty → sel c S ∈ S) {n k : ℕ} (G : SimpleGraph (Fin n))
    (C : G.Coloring (Fin k)) (c : List ℕ) (hc : Traj θ sel G c) :
    Ev (pairs c) c ∧ Set.InjOn Prod.fst (↑(pairs c) : Set (ℕ × ℕ)) ∧
      Set.InjOn Prod.snd (↑(pairs c) : Set (ℕ × ℕ)) ∧
      ∀ p ∈ pairs c, p.2 ∈ Last G (phiN C) ((pairs c).image Prod.snd) p.1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    have h := (mem_pairs c p).mp hp
    refine ⟨h.2.2.1, fun _ => ⟨?_, h.2.2.2.1.symm⟩⟩
    rw [count_take_eq, Finset.card_eq_one]
    refine ⟨p.1, ?_⟩
    ext u
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hu, hub, hue⟩
      rcases pair_pos c p hp u hu hue with e | e
      · exact e
      · omega
    · rintro rfl
      exact ⟨h.1, h.2.2.1, rfl⟩
  · intro p hp q hq he
    exact pair_eq c p q hp hq (by rw [he])
  · intro p hp q hq he
    have hq' := (mem_pairs c q).mp hq
    have hp' := (mem_pairs c p).mp hp
    exact pair_eq c p q hp hq (by rw [hq'.2.2.2.1, hp'.2.2.2.1]; rw [he])
  · intro p hp
    have h := (mem_pairs c p).mp hp
    obtain ⟨ha, hb, hab, he, hcount⟩ := h
    have hbn : p.2 < n := lt_of_lt_of_le hb hc.1
    simp only [Last, Finset.mem_filter]
    refine ⟨Finset.mem_image.mpr ⟨p, hp, rfl⟩, ?_, ?_⟩
    · intro hadj
      rcases traj_cases hsel hc p.2 hb with hh | hh
      · exact hh.2.2.1 p.1 hab (prefixAdj_of_adjN G p.1 p.2 hbn hab hadj)
          (by rw [getD_take_of_lt c p.2 p.1 hab, he])
      · exact hh.1 (by rw [← he]; exact getD_mem_take c p.2 p.1 hab ha)
    · intro b' hb' hbb' hphi
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb'
      have hq' := (mem_pairs c q).mp hq
      have hqn : q.2 < n := lt_of_lt_of_le hq'.2.1 hc.1
      by_contra hna
      have hnb : ¬ adjN G p.2 q.2 := fun h' => phiN_ne_of_adjN C _ _ h' hphi.symm
      -- the color of `p` is an eligible level-2 color at the arrival of `q.2`
      have hE2 : (eligibleLevel G ⟨q.2, lt_of_lt_of_le hq'.2.1 hc.1⟩
          (c.take q.2) 2).Nonempty := by
        refine ⟨c.getD p.1 0, ?_⟩
        simp only [eligibleLevel, Finset.mem_filter, List.mem_toFinset]
        refine ⟨getD_mem_take c q.2 p.1 (by omega) ha, ?_, ?_⟩
        · rw [count_take_eq, ← hcount, count_eq_card_pos]
          congr 1
          apply Finset.filter_congr
          intro u hu
          constructor
          · exact fun h' => h'.2
          · intro h'
            refine ⟨?_, h'⟩
            rcases pair_pos c p hp u (Finset.mem_range.mp hu) h' with e | e <;> omega
        · intro u hu hadj heq
          have hu' : u < q.2 := hu
          rw [getD_take_of_lt c q.2 u hu'] at heq
          have hadj' := adjN_of_prefixAdj G u q.2 hqn hadj
          rcases pair_pos c p hp u (by omega) heq with e | e
          · subst e; exact hna hadj'
          · subst e; exact hnb hadj'
      rcases traj_cases hsel hc q.2 hq'.2.1 with hh | hh
      · have h2 := hh.2.2.2 hE2
        rw [count_take_eq] at h2
        have hsub : (Finset.range c.length).filter
            (fun i => i < q.2 ∧ c.getD i 0 = c.getD q.2 0) ⊆ {q.1} := by
          intro u hu
          simp only [Finset.mem_filter, Finset.mem_range] at hu
          rcases pair_pos c q hq u hu.1 (by rw [hu.2.2, hq'.2.2.2.1]) with e | e
          · simp [e]
          · omega
        have := Finset.card_le_card hsub
        rw [Finset.card_singleton] at this
        omega
      · exact hh.2.1 hE2

end OnlineColoringKYY.Supplement.Dev.T55.PartA
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T55
open Classical OnlineColoringKYY.Supplement
alias pairs_structure := OnlineColoringKYY.Supplement.Dev.T55.PartA.pairs_structure

end OnlineColoringKYY.Supplement.Dev.T55
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T55.PartPE
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T55
/-! ### Basic helpers -/
theorem outer_le_one {α : Type*} (p : PMF α) (s : Set α) : p.toOuterMeasure s ≤ 1 := by
  calc p.toOuterMeasure s ≤ p.toOuterMeasure Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
    _ = 1 := (p.toOuterMeasure_apply_eq_one_iff _).2 (Set.subset_univ _)

theorem lt_freshColor (c : List ℕ) : ∀ x ∈ c, x < freshColor c := by
  induction c with
  | nil => simp
  | cons y l ih =>
    intro x hx
    simp only [freshColor, List.foldr_cons] at *
    rcases List.mem_cons.1 hx with rfl | hx
    · exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
    · exact lt_of_lt_of_le (ih x hx) (le_max_right _ _)

theorem run_length (θ : ℕ) (sel : List ℕ → Finset ℕ → ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∀ (m : ℕ) (h : m ≤ n) (c : List ℕ), threeLevelRun θ sel G m h c ≠ 0 → c.length = m := by
  intro m
  induction m with
  | zero =>
    intro h c hc
    simp only [threeLevelRun, PMF.pure_apply, ne_eq, ite_eq_right_iff, not_forall] at hc
    obtain ⟨rfl, _⟩ := hc
    rfl
  | succ m ih =>
    intro h c hc
    have hc' : c ∈ (threeLevelRun θ sel G (m+1) h).support := hc
    simp only [threeLevelRun, PMF.mem_support_bind_iff, PMF.support_map, Set.mem_image] at hc'
    obtain ⟨d, hd, x, _, rfl⟩ := hc'
    simp [ih _ d hd]

theorem step_le (θ : ℕ) (sel : List ℕ → Finset ℕ → ℕ)
    (hsel : ∀ c S, S.Nonempty → sel c S ∈ S) {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    (c : List ℕ) (y : ℕ) (hy : c.count y = 1) :
    threeLevelStep θ sel G v c y ≤ (θ : ENNReal)⁻¹ := by
  have hyc : y ∈ c := List.count_pos_iff.1 (by omega)
  unfold threeLevelStep
  split_ifs with h2 h1
  · have hm := hsel c _ h2
    have hne : y ≠ sel c (eligibleLevel G v c 2) := by
      intro he
      have hm2 : c.count (sel c (eligibleLevel G v c 2)) = 2 := (Finset.mem_filter.1 hm).2.1
      rw [← he] at hm2
      omega
    simp [PMF.pure_apply, hne]
  · rw [PMF.uniformOfFinset_apply]
    split_ifs
    · exact ENNReal.inv_le_inv.2 (by exact_mod_cast h1.2)
    · exact bot_le
  · have hne : y ≠ freshColor c := fun he => by
      have := lt_freshColor c y hyc
      omega
    simp [PMF.pure_apply, hne]

theorem Ev_of_append (P : Finset (ℕ × ℕ)) (c : List ℕ) (x : ℕ) (h : Ev P (c ++ [x])) : Ev P c := by
  intro p hp
  obtain ⟨h1, h2⟩ := h p hp
  refine ⟨h1, fun hlt => ?_⟩
  have hl : p.2 < (c ++ [x]).length := by simp; omega
  obtain ⟨h3, h4⟩ := h2 hl
  have e1 : (c ++ [x]).take p.2 = c.take p.2 := List.take_append_of_le_length hlt.le
  have e2 : (c ++ [x]).getD p.1 0 = c.getD p.1 0 := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show p.1 < c.length by omega)]
  have e3 : (c ++ [x]).getD p.2 0 = c.getD p.2 0 := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
  rw [e1, e2] at h3
  rw [e3, e2] at h4
  exact ⟨h3, h4⟩

theorem Ev_append_last (P : Finset (ℕ × ℕ)) (c : List ℕ) (x : ℕ) (p : ℕ × ℕ) (hp : p ∈ P)
    (hpm : p.2 = c.length) (h : Ev P (c ++ [x])) :
    c.count (c.getD p.1 0) = 1 ∧ x = c.getD p.1 0 := by
  obtain ⟨h1, h2⟩ := h p hp
  have hl : p.2 < (c ++ [x]).length := by simp; omega
  obtain ⟨h3, h4⟩ := h2 hl
  have e1 : (c ++ [x]).take p.2 = c := by rw [hpm]; simp
  have e2 : (c ++ [x]).getD p.1 0 = c.getD p.1 0 := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show p.1 < c.length by omega)]
  have e3 : (c ++ [x]).getD p.2 0 = x := by
    simp [List.getD_eq_getElem?_getD, hpm]
  rw [e1, e2] at h3
  rw [e3, e2] at h4
  exact ⟨h3, h4⟩

theorem prob_Ev_le (θ : ℕ) (hθ : 1 ≤ θ) (sel : List ℕ → Finset ℕ → ℕ)
    (hsel : ∀ c S, S.Nonempty → sel c S ∈ S) {n : ℕ} (G : SimpleGraph (Fin n))
    (P : Finset (ℕ × ℕ)) (hP : Set.InjOn Prod.snd (↑P : Set (ℕ × ℕ)))
    (m : ℕ) (h : m ≤ n) :
    (threeLevelRun θ sel G m h).toOuterMeasure {c | Ev P c} ≤
      ((θ : ENNReal)⁻¹) ^ (P.filter (fun p => p.2 < m)).card := by
  induction m with
  | zero =>
    have : P.filter (fun p => p.2 < 0) = ∅ := by
      ext q; simp
    rw [this, Finset.card_empty, pow_zero]
    exact outer_le_one _ _
  | succ m ih =>
    have ih' := ih (Nat.le_of_succ_le h)
    set μ := threeLevelRun θ sel G m (Nat.le_of_succ_le h) with hμdef
    set r : ENNReal := if ∃ p ∈ P, p.2 = m then (θ : ENNReal)⁻¹ else 1 with hr
    have hcard : ((θ : ENNReal)⁻¹) ^ (P.filter (fun p => p.2 < m)).card * r ≤
        ((θ : ENNReal)⁻¹) ^ (P.filter (fun p => p.2 < m + 1)).card := by
      by_cases hex : ∃ p ∈ P, p.2 = m
      · obtain ⟨p0, hp0, hp0m⟩ := hex
        have hr' : r = (θ : ENNReal)⁻¹ := if_pos ⟨p0, hp0, hp0m⟩
        have heq : P.filter (fun p => p.2 < m + 1) = insert p0 (P.filter (fun p => p.2 < m)) := by
          ext q
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hq, hqm⟩
            by_cases hq2 : q.2 = m
            · left; exact hP hq hp0 (hq2.trans hp0m.symm)
            · right; exact ⟨hq, by omega⟩
          · rintro (rfl | ⟨hq, hqm⟩)
            · exact ⟨hp0, by omega⟩
            · exact ⟨hq, by omega⟩
        have hnot : p0 ∉ P.filter (fun p => p.2 < m) := by
          simp [Finset.mem_filter, hp0m]
        rw [heq, Finset.card_insert_of_notMem hnot, pow_succ, hr']
      · have hr' : r = 1 := if_neg hex
        have heq : P.filter (fun p => p.2 < m + 1) = P.filter (fun p => p.2 < m) := by
          ext q
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hq, hqm⟩
            refine ⟨hq, ?_⟩
            by_contra hc
            exact hex ⟨q, hq, by omega⟩
          · rintro ⟨hq, hqm⟩; exact ⟨hq, by omega⟩
        rw [heq, hr', mul_one]
    have key : ∀ c, μ c * (threeLevelStep θ sel G ⟨m, h⟩ c).toOuterMeasure
        ((fun x => c ++ [x]) ⁻¹' {c | Ev P c}) ≤ ({c | Ev P c}.indicator μ c) * r := by
      intro c
      by_cases hμ : μ c = 0
      · simp [hμ]
      have hlen := run_length θ sel G m (Nat.le_of_succ_le h) c hμ
      by_cases hE : Ev P c
      · rw [Set.indicator_of_mem (show c ∈ {c | Ev P c} from hE)]
        gcongr
        by_cases hex : ∃ p ∈ P, p.2 = m
        · obtain ⟨p0, hp0, hp0m⟩ := hex
          have hr' : r = (θ : ENNReal)⁻¹ := if_pos ⟨p0, hp0, hp0m⟩
          rw [hr']
          by_cases hc1 : c.count (c.getD p0.1 0) = 1
          · have hsub : ((fun x => c ++ [x]) ⁻¹' {c | Ev P c}) ⊆ {c.getD p0.1 0} := by
              intro x hx
              exact (Ev_append_last P c x p0 hp0 (hp0m.trans hlen.symm) hx).2
            calc _ ≤ (threeLevelStep θ sel G ⟨m, h⟩ c).toOuterMeasure {c.getD p0.1 0} :=
                  MeasureTheory.measure_mono hsub
              _ = threeLevelStep θ sel G ⟨m, h⟩ c (c.getD p0.1 0) :=
                  PMF.toOuterMeasure_apply_singleton _ _
              _ ≤ _ := step_le θ sel hsel G _ c _ hc1
          · have hemp : ((fun x => c ++ [x]) ⁻¹' {c | Ev P c}) = ∅ := by
              ext x
              simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
              intro hx
              exact hc1 (Ev_append_last P c x p0 hp0 (hp0m.trans hlen.symm) hx).1
            rw [hemp, MeasureTheory.measure_empty]
            exact bot_le
        · have hr' : r = 1 := if_neg hex
          rw [hr']
          exact outer_le_one _ _
      · have hemp : ((fun x => c ++ [x]) ⁻¹' {c | Ev P c}) = ∅ := by
          ext x
          simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          intro hx
          exact hE (Ev_of_append P c x hx)
        rw [hemp, MeasureTheory.measure_empty, mul_zero]
        exact bot_le
    calc (threeLevelRun θ sel G (m + 1) h).toOuterMeasure {c | Ev P c}
        = ∑' c, μ c * ((threeLevelStep θ sel G ⟨m, h⟩ c).map (fun x => c ++ [x])).toOuterMeasure
            {c | Ev P c} := by
          rw [threeLevelRun, PMF.toOuterMeasure_bind_apply]
      _ = ∑' c, μ c * (threeLevelStep θ sel G ⟨m, h⟩ c).toOuterMeasure
            ((fun x => c ++ [x]) ⁻¹' {c | Ev P c}) := by
          simp_rw [PMF.toOuterMeasure_map_apply]
      _ ≤ ∑' c, ({c | Ev P c}.indicator μ c) * r := ENNReal.tsum_le_tsum key
      _ = (∑' c, {c | Ev P c}.indicator μ c) * r := ENNReal.tsum_mul_right
      _ = μ.toOuterMeasure {c | Ev P c} * r := by rw [PMF.toOuterMeasure_apply]
      _ ≤ ((θ : ENNReal)⁻¹) ^ (P.filter (fun p => p.2 < m)).card * r := by gcongr
      _ ≤ _ := hcard

end OnlineColoringKYY.Supplement.Dev.T55.PartPE
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T55
open Classical OnlineColoringKYY.Supplement
/-! ### Part P: probability of a fixed pairing (paper's Lemma 5.2) -/

end OnlineColoringKYY.Supplement.Dev.T55
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T55.PartPE
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T55
theorem mem_pairOf (A : Finset ℕ) (f : (a : ℕ) → a ∈ A → ℕ) (q : ℕ × ℕ) :
    q ∈ pairOf A f ↔ ∃ (a : ℕ) (ha : a ∈ A), q = (a, f a ha) := by
  unfold pairOf
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨a, ha⟩, _, rfl⟩; exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩; exact ⟨⟨a, ha⟩, Finset.mem_attach _ _, rfl⟩

theorem card_pairOf (A : Finset ℕ) (f : (a : ℕ) → a ∈ A → ℕ) : (pairOf A f).card = A.card := by
  unfold pairOf
  rw [Finset.card_image_of_injective, Finset.card_attach]
  intro a b hab
  exact Subtype.ext (congrArg Prod.fst hab)

theorem prob_lvl_two_eq (θ : ℕ) (hθ : 1 ≤ θ) (sel : List ℕ → Finset ℕ → ℕ)
    (hsel : ∀ c S, S.Nonempty → sel c S ∈ S) {n k : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.Colorable k) (m : ℕ) :
    (threeLevelRun θ sel G n le_rfl).toOuterMeasure {c | lvl c 2 = m} ≤
      ((n.choose m : ENNReal)) ^ 2 * (k : ENNReal) ^ m * ((θ : ENNReal)⁻¹) ^ m := by
  obtain ⟨C⟩ := hG
  set μ := threeLevelRun θ sel G n le_rfl with hμdef
  set S := (Finset.range n).powersetCard m with hS
  have hcover : ∀ c, {c | lvl c 2 = m}.indicator μ c ≤
      ∑ A ∈ S, ∑ B ∈ S, ∑ f ∈ A.pi (fun a => Last G (phiN C) B a),
        (if Set.InjOn Prod.snd (↑(pairOf A f) : Set (ℕ × ℕ)) then
          {c | Ev (pairOf A f) c}.indicator μ c else 0) := by
    intro c
    by_cases hlv : lvl c 2 = m
    swap
    · rw [Set.indicator_of_notMem (show c ∉ {c | lvl c 2 = m} from hlv)]
      exact bot_le
    rw [Set.indicator_of_mem (show c ∈ {c | lvl c 2 = m} from hlv)]
    by_cases hμ : μ c = 0
    · rw [hμ]; exact bot_le
    obtain ⟨hlen, htraj⟩ := run_support θ sel G n le_rfl c ((PMF.mem_support_iff _ _).2 hμ)
    obtain ⟨hEv, hinj1, hinj2, hLast⟩ := pairs_structure θ sel hsel G C c htraj
    have hrange : ∀ q ∈ pairs c, q.1 < n ∧ q.2 < n := by
      intro q hq
      have := (Finset.mem_filter.1 hq).1
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at this
      omega
    set A := (pairs c).image Prod.fst with hA
    set B := (pairs c).image Prod.snd with hB
    have hex : ∀ a ∈ A, ∃ b, (a, b) ∈ pairs c := by
      intro a ha
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 ha
      exact ⟨q.2, hq⟩
    let f : (a : ℕ) → a ∈ A → ℕ := fun a ha => Classical.choose (hex a ha)
    have hf : ∀ a (ha : a ∈ A), (a, f a ha) ∈ pairs c := fun a ha => Classical.choose_spec (hex a ha)
    have hpair : pairOf A f = pairs c := by
      ext q
      rw [mem_pairOf]
      constructor
      · rintro ⟨a, ha, rfl⟩; exact hf a ha
      · intro hq
        have hq1 : q.1 ∈ A := Finset.mem_image_of_mem _ hq
        refine ⟨q.1, hq1, ?_⟩
        exact hinj1 (Finset.mem_coe.2 hq) (Finset.mem_coe.2 (hf q.1 hq1)) rfl
    have hAS : A ∈ S := by
      rw [hS, Finset.mem_powersetCard]
      refine ⟨fun a ha => ?_, ?_⟩
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 ha
        exact Finset.mem_range.2 (hrange q hq).1
      · rw [hA, Finset.card_image_of_injOn hinj1, card_pairs, hlv]
    have hBS : B ∈ S := by
      rw [hS, Finset.mem_powersetCard]
      refine ⟨fun a ha => ?_, ?_⟩
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 ha
        exact Finset.mem_range.2 (hrange q hq).2
      · rw [hB, Finset.card_image_of_injOn hinj2, card_pairs, hlv]
    have hfpi : f ∈ A.pi (fun a => Last G (phiN C) B a) := by
      rw [Finset.mem_pi]
      intro a ha
      exact hLast _ (hf a ha)
    have hterm : (if Set.InjOn Prod.snd (↑(pairOf A f) : Set (ℕ × ℕ)) then
          {c | Ev (pairOf A f) c}.indicator μ c else 0) = μ c := by
      rw [hpair, if_pos hinj2, Set.indicator_of_mem (show c ∈ {d | Ev (pairs c) d} from hEv)]
    refine le_trans (le_of_eq hterm.symm) ?_
    refine le_trans ?_ (Finset.single_le_sum (fun _ _ => by simp) hAS)
    refine le_trans ?_ (Finset.single_le_sum (fun _ _ => by simp) hBS)
    exact Finset.single_le_sum (f := fun g => if Set.InjOn Prod.snd (↑(pairOf A g) : Set (ℕ × ℕ))
      then {d | Ev (pairOf A g) d}.indicator μ c else 0) (fun _ _ => zero_le) hfpi
  have hterm : ∀ A ∈ S, ∀ B ∈ S, ∀ f ∈ A.pi (fun a => Last G (phiN C) B a),
      ∑' c, (if Set.InjOn Prod.snd (↑(pairOf A f) : Set (ℕ × ℕ)) then
          {c | Ev (pairOf A f) c}.indicator μ c else 0) ≤ ((θ : ENNReal)⁻¹) ^ m := by
    intro A hA B hB f hf
    split_ifs with hinj
    · rw [← PMF.toOuterMeasure_apply]
      have hfilt : (pairOf A f).filter (fun p => p.2 < n) = pairOf A f := by
        apply Finset.filter_true_of_mem
        intro q hq
        obtain ⟨a, ha, rfl⟩ := (mem_pairOf A f q).1 hq
        have h1 := (Finset.mem_pi.1 hf) a ha
        have h2 : f a ha ∈ B := (Finset.mem_filter.1 h1).1
        have h3 := (Finset.mem_powersetCard.1 hB).1 h2
        exact Finset.mem_range.1 h3
      have := prob_Ev_le θ hθ sel hsel G (pairOf A f) hinj n le_rfl
      rw [hfilt, card_pairOf, (Finset.mem_powersetCard.1 hA).2] at this
      exact this
    · simp
  have hpicard : ∀ A ∈ S, ∀ B ∈ S, ((A.pi (fun a => Last G (phiN C) B a)).card : ENNReal) ≤
      (k : ENNReal) ^ m := by
    intro A hA B hB
    rw [Finset.card_pi]
    have : ∏ a ∈ A, (Last G (phiN C) B a).card ≤ k ^ m := by
      rw [← (Finset.mem_powersetCard.1 hA).2]
      apply Finset.prod_le_pow_card
      intro a _
      apply card_Last_le
      intro b hb
      exact Finset.mem_range.1 ((Finset.mem_powersetCard.1 hB).1 hb)
    exact_mod_cast this
  calc μ.toOuterMeasure {c | lvl c 2 = m} = ∑' c, {c | lvl c 2 = m}.indicator μ c :=
        PMF.toOuterMeasure_apply _ _
    _ ≤ ∑' c, ∑ A ∈ S, ∑ B ∈ S, ∑ f ∈ A.pi (fun a => Last G (phiN C) B a),
        (if Set.InjOn Prod.snd (↑(pairOf A f) : Set (ℕ × ℕ)) then
          {c | Ev (pairOf A f) c}.indicator μ c else 0) := ENNReal.tsum_le_tsum hcover
    _ = ∑ A ∈ S, ∑ B ∈ S, ∑ f ∈ A.pi (fun a => Last G (phiN C) B a), ∑' c,
        (if Set.InjOn Prod.snd (↑(pairOf A f) : Set (ℕ × ℕ)) then
          {c | Ev (pairOf A f) c}.indicator μ c else 0) := by
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        refine Finset.sum_congr rfl (fun A _ => ?_)
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        refine Finset.sum_congr rfl (fun B _ => ?_)
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    _ ≤ ∑ A ∈ S, ∑ B ∈ S, ∑ f ∈ A.pi (fun a => Last G (phiN C) B a), ((θ : ENNReal)⁻¹) ^ m := by
        gcongr with A hA B hB f hf
        exact hterm A hA B hB f hf
    _ = ∑ A ∈ S, ∑ B ∈ S, ((A.pi (fun a => Last G (phiN C) B a)).card : ENNReal) *
          ((θ : ENNReal)⁻¹) ^ m := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ A ∈ S, ∑ B ∈ S, (k : ENNReal) ^ m * ((θ : ENNReal)⁻¹) ^ m := by
        gcongr with A hA B hB
        exact hpicard A hA B hB
    _ = ((n.choose m : ENNReal)) ^ 2 * (k : ENNReal) ^ m * ((θ : ENNReal)⁻¹) ^ m := by
        simp only [Finset.sum_const, nsmul_eq_mul, hS, Finset.card_powersetCard, Finset.card_range]
        ring

end OnlineColoringKYY.Supplement.Dev.T55.PartPE
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T55
open Classical OnlineColoringKYY.Supplement
/-! ### Part E: counting (Lemma 5.3) and expectation (Lemma 5.4 and Theorem 5.5's identity) -/

end OnlineColoringKYY.Supplement.Dev.T55
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T55.PartPE
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T55
theorem tsum_geom_two : ∑' j : ℕ, ((2 : ENNReal)⁻¹) ^ j * (j : ENNReal) = 2 := by
  have hr : ‖(1 / 2 : ℝ)‖ < 1 := by norm_num
  have hR : ∑' j : ℕ, (j : ℝ) * (1 / 2 : ℝ) ^ j = 2 := by
    rw [tsum_coe_mul_geometric_of_norm_lt_one hr]; norm_num
  have hS : Summable (fun j : ℕ => (j : ℝ) * (1 / 2 : ℝ) ^ j) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hr).summable
  have hterm : ∀ j : ℕ, ((2 : ENNReal)⁻¹) ^ j * (j : ENNReal) =
      ENNReal.ofReal ((j : ℝ) * (1 / 2 : ℝ) ^ j) := by
    intro j
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_natCast, mul_comm, one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
    simp
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hS, hR]
  simp

theorem expColors_le (θ : ℕ) (hθ : 1 ≤ θ) (sel : List ℕ → Finset ℕ → ℕ)
    (hsel : ∀ c S, S.Nonempty → sel c S ∈ S) {n k : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.Colorable k) (m₀ : ℕ)
    (htail : ∀ m, m₀ ≤ m →
      ((n.choose m : ENNReal)) ^ 2 * (k : ENNReal) ^ m * ((θ : ENNReal)⁻¹) ^ m ≤ (2⁻¹) ^ m) :
    expColors (threeLevelRun θ sel G n le_rfl) ≤
      ((n : ENNReal) + 2 * k * θ + m₀ + 2) / 3 := by
  set μ := threeLevelRun θ sel G n le_rfl with hμdef
  -- probability of `lvl c 2 = j`
  set Pr : ℕ → ENNReal := fun j => ∑' c, {c | lvl c 2 = j}.indicator μ c with hPr
  have hPr_le : ∀ j, m₀ ≤ j → Pr j ≤ (2⁻¹) ^ j := by
    intro j hj
    have := prob_lvl_two_eq θ hθ sel hsel G hG j
    rw [PMF.toOuterMeasure_apply] at this
    exact this.trans (htail j hj)
  have hPr_sum : ∑' j, Pr j = 1 := by
    simp only [hPr]
    rw [ENNReal.tsum_comm]
    rw [← PMF.tsum_coe μ]
    refine tsum_congr (fun c => ?_)
    rw [tsum_eq_single (lvl c 2)]
    · exact Set.indicator_of_mem (show c ∈ {d | lvl d 2 = lvl c 2} from rfl) _
    · intro j hj
      exact Set.indicator_of_notMem (show c ∉ {d | lvl d 2 = j} from fun h => hj h.symm) _
  have hL : ∑' c, μ c * (lvl c 2 : ENNReal) ≤ m₀ + 2 := by
    have e1 : ∀ c, μ c * (lvl c 2 : ENNReal) =
        ∑' j, {c | lvl c 2 = j}.indicator μ c * (j : ENNReal) := by
      intro c
      rw [tsum_eq_single (lvl c 2)]
      · rw [Set.indicator_of_mem (show c ∈ {d | lvl d 2 = lvl c 2} from rfl)]
      · intro j hj
        rw [Set.indicator_of_notMem (show c ∉ {d | lvl d 2 = j} from fun h => hj h.symm), zero_mul]
    calc ∑' c, μ c * (lvl c 2 : ENNReal)
        = ∑' c, ∑' j, {c | lvl c 2 = j}.indicator μ c * (j : ENNReal) := tsum_congr e1
      _ = ∑' j, ∑' c, {c | lvl c 2 = j}.indicator μ c * (j : ENNReal) := ENNReal.tsum_comm
      _ = ∑' j, Pr j * (j : ENNReal) := by
          refine tsum_congr (fun j => ?_)
          rw [ENNReal.tsum_mul_right]
      _ ≤ ∑' j, (Pr j * (m₀ : ENNReal) + ((2 : ENNReal)⁻¹) ^ j * (j : ENNReal)) := by
          refine ENNReal.tsum_le_tsum (fun j => ?_)
          by_cases hj : j < m₀
          · calc Pr j * (j : ENNReal) ≤ Pr j * (m₀ : ENNReal) := by
                  gcongr
              _ ≤ _ := le_self_add
          · calc Pr j * (j : ENNReal) ≤ ((2 : ENNReal)⁻¹) ^ j * (j : ENNReal) := by
                  gcongr
                  exact hPr_le j (by omega)
              _ ≤ _ := le_add_self
      _ = (∑' j, Pr j) * (m₀ : ENNReal) + ∑' j : ℕ, ((2 : ENNReal)⁻¹) ^ j * (j : ENNReal) := by
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
      _ = m₀ + 2 := by rw [hPr_sum, one_mul, tsum_geom_two]
  have hpt : ∀ c, μ c * ((3 * c.toFinset.card : ℕ) : ENNReal) ≤
      μ c * ((n + 2 * k * θ : ℕ) : ENNReal) + μ c * (lvl c 2 : ENNReal) := by
    intro c
    by_cases hμ : μ c = 0
    · simp [hμ]
    obtain ⟨hlen, htraj⟩ := run_support θ sel G n le_rfl c ((PMF.mem_support_iff _ _).2 hμ)
    have h3 := card_toFinset_eq c (count_le_three θ sel hsel G c htraj)
    have h1 := lvl_one_le θ hθ sel hsel G hG c htraj
    have hle : 3 * c.toFinset.card ≤ (n + 2 * k * θ) + lvl c 2 := by
      rw [h3, hlen]
      have : 2 * lvl c 1 ≤ 2 * (k * θ) := Nat.mul_le_mul_left 2 h1
      rw [mul_assoc]; omega
    rw [← mul_add]
    gcongr
    exact_mod_cast hle
  have h3E : expColors μ * 3 ≤ (n : ENNReal) + 2 * k * θ + m₀ + 2 := by
    unfold expColors
    calc (∑' c, μ c * (c.toFinset.card : ENNReal)) * 3
        = ∑' c, μ c * ((3 * c.toFinset.card : ℕ) : ENNReal) := by
          rw [← ENNReal.tsum_mul_right]
          refine tsum_congr (fun c => ?_)
          push_cast; ring
      _ ≤ ∑' c, (μ c * ((n + 2 * k * θ : ℕ) : ENNReal) + μ c * (lvl c 2 : ENNReal)) :=
          ENNReal.tsum_le_tsum hpt
      _ = (∑' c, μ c) * ((n + 2 * k * θ : ℕ) : ENNReal) + ∑' c, μ c * (lvl c 2 : ENNReal) := by
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
      _ ≤ 1 * ((n + 2 * k * θ : ℕ) : ENNReal) + (m₀ + 2) := by
          rw [PMF.tsum_coe]
          gcongr
      _ = (n : ENNReal) + 2 * k * θ + m₀ + 2 := by push_cast; ring
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))]
  exact h3E

end OnlineColoringKYY.Supplement.Dev.T55.PartPE
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T55
open Classical OnlineColoringKYY.Supplement
alias expColors_le := OnlineColoringKYY.Supplement.Dev.T55.PartPE.expColors_le

end OnlineColoringKYY.Supplement.Dev.T55
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T55.PartPE
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T55
/-- The trivial bound: at most `n` colors. -/
theorem expColors_le_n (θ : ℕ) (sel : List ℕ → Finset ℕ → ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) :
    expColors (threeLevelRun θ sel G n le_rfl) ≤ n := by
  unfold expColors
  calc ∑' c, threeLevelRun θ sel G n le_rfl c * (c.toFinset.card : ENNReal)
      ≤ ∑' c, threeLevelRun θ sel G n le_rfl c * (n : ENNReal) := by
        refine ENNReal.tsum_le_tsum (fun c => ?_)
        by_cases hμ : threeLevelRun θ sel G n le_rfl c = 0
        · simp [hμ]
        have hlen := run_length θ sel G n le_rfl c hμ
        gcongr
        exact_mod_cast (List.toFinset_card_le c).trans hlen.le
    _ = n := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end OnlineColoringKYY.Supplement.Dev.T55.PartPE
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T55
open Classical OnlineColoringKYY.Supplement
alias expColors_le_n := OnlineColoringKYY.Supplement.Dev.T55.PartPE.expColors_le_n

end OnlineColoringKYY.Supplement.Dev.T55
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T55.PartR
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T55
lemma cube_root_cube (x : ℝ) (hx : 0 ≤ x) : (x ^ ((1 : ℝ) / 3)) ^ 3 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

lemma two_thirds (x : ℝ) (hx : 0 ≤ x) : x ^ ((2 : ℝ) / 3) = (x ^ ((1 : ℝ) / 3)) ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

/-- The trivial range `n ≤ k²` (with `n ≥ 1`): `n ≤ n/3 + 4 n^{2/3} k^{2/3}`. -/
theorem trivial_range (n k : ℕ) (hkn : n ≤ k ^ 2) :
    (n : ℝ) ≤ (n : ℝ) / 3 + 4 * (n : ℝ) ^ ((2 : ℝ) / 3) * (k : ℝ) ^ ((2 : ℝ) / 3) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rw [two_thirds _ hn0, two_thirds _ hk0]
  set a := (n : ℝ) ^ ((1 : ℝ) / 3) with ha
  set b := (k : ℝ) ^ ((1 : ℝ) / 3) with hb
  have ha0 : 0 ≤ a := Real.rpow_nonneg hn0 _
  have hb0 : 0 ≤ b := Real.rpow_nonneg hk0 _
  have ha3 : a ^ 3 = n := cube_root_cube _ hn0
  have hb3 : b ^ 3 = k := cube_root_cube _ hk0
  have hab : a ≤ b ^ 2 := by
    apply le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (by positivity)
    rw [ha3, ← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, hb3]
    exact_mod_cast hkn
  have : (n : ℝ) ≤ a ^ 2 * b ^ 2 := by
    rw [← ha3, show a ^ 3 = a ^ 2 * a by ring]
    exact mul_le_mul_of_nonneg_left hab (by positivity)
  linarith

/-- The parameter choice in the nontrivial range `k² < n`: with `T = n^{2/3} k^{2/3}`,
`θ = ⌈(n²/k)^{1/3}⌉`, `m₀ = ⌈4T⌉`. -/
theorem params (n k : ℕ) (hk : 1 ≤ k) (hkn : k ^ 2 < n) :
    ∃ θ m₀ : ℕ, 1 ≤ θ ∧
      (∀ m, m₀ ≤ m →
        ((n.choose m : ENNReal)) ^ 2 * (k : ENNReal) ^ m * ((θ : ENNReal)⁻¹) ^ m ≤ (2⁻¹) ^ m) ∧
      ((n : ℝ) + 2 * k * θ + m₀ + 2) / 3 ≤
        (n : ℝ) / 3 + 4 * (n : ℝ) ^ ((2 : ℝ) / 3) * (k : ℝ) ^ ((2 : ℝ) / 3) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rw [two_thirds _ hn0, two_thirds _ hk0]
  set a := (n : ℝ) ^ ((1 : ℝ) / 3) with ha
  set b := (k : ℝ) ^ ((1 : ℝ) / 3) with hb
  have ha0 : 0 ≤ a := Real.rpow_nonneg hn0 _
  have hb0 : 0 ≤ b := Real.rpow_nonneg hk0 _
  have ha3 : a ^ 3 = n := cube_root_cube _ hn0
  have hb3 : b ^ 3 = k := cube_root_cube _ hk0
  have hb1 : 1 ≤ b := by
    apply le_of_pow_le_pow_left₀ (n := 3) (by norm_num) hb0
    rw [hb3, one_pow]; exact_mod_cast hk
  have hab : b ^ 2 < a := by
    apply lt_of_pow_lt_pow_left₀ 3 ha0
    rw [ha3, ← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, hb3]
    exact_mod_cast hkn
  have hb2 : b ≤ b ^ 2 := by nlinarith
  have ha1 : 1 < a := by nlinarith
  have ha2 : a ≤ a ^ 2 := by nlinarith
  have hbpos : 0 < b := by linarith
  set r := a ^ 2 / b with hr
  have hr1 : 1 ≤ r := by rw [hr, le_div_iff₀ hbpos]; linarith
  set T := a ^ 2 * b ^ 2 with hT
  have hkr : (k : ℝ) * r = T := by rw [← hb3, hr, hT]; field_simp
  have hrT : r * T ^ 2 = (n : ℝ) ^ 2 * k := by
    rw [← hb3, ← ha3, hr, hT]; field_simp
  have hkT : (k : ℝ) ≤ T := by
    rw [← hb3, hT, show b ^ 3 = b * b ^ 2 by ring]
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hT1 : 1 ≤ T := one_le_mul_of_one_le_of_one_le (by nlinarith) (by nlinarith)
  refine ⟨⌈r⌉₊, ⌈4 * T⌉₊, ?_, ?_, ?_⟩
  · have := Nat.le_ceil r
    exact_mod_cast (hr1.trans this)
  · intro m hm
    have hθr : r ≤ (⌈r⌉₊ : ℝ) := Nat.le_ceil r
    have hmT : 4 * T ≤ m := (Nat.ceil_le).1 hm
    have hmpos : (0 : ℝ) < m := by linarith
    set θ := ⌈r⌉₊ with hθ
    set X := (n : ℝ) * Real.exp 1 / m with hX
    have hX0 : 0 ≤ X := by positivity
    have hC : ((n.choose m : ℕ) : ℝ) ≤ X ^ m := by
      refine (Nat.choose_le_pow_div m n).trans ?_
      have h2 := Real.pow_div_factorial_le_exp (m : ℝ) hmpos.le m
      rw [← Real.exp_one_pow, div_le_iff₀ (by positivity)] at h2
      rw [hX, div_pow, mul_pow, le_div_iff₀ (by positivity)]
      calc (n : ℝ) ^ m / (m.factorial : ℝ) * (m : ℝ) ^ m
          = (n : ℝ) ^ m * ((m : ℝ) ^ m / (m.factorial : ℝ)) := by ring
        _ ≤ (n : ℝ) ^ m * (Real.exp 1 ^ m) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_iff₀ (by positivity)]; exact h2
    have hE : Real.exp 1 ^ 2 ≤ 8 := by
      have := Real.exp_one_lt_d9
      nlinarith [Real.exp_pos 1]
    have hbase : X ^ 2 * k * 2 ≤ θ := by
      rw [hX, div_pow, mul_pow]
      rw [show (n : ℝ) ^ 2 * Real.exp 1 ^ 2 / (m : ℝ) ^ 2 * k * 2
          = ((n : ℝ) ^ 2 * k * (2 * Real.exp 1 ^ 2)) / (m : ℝ) ^ 2 by ring]
      rw [div_le_iff₀ (by positivity)]
      have hm2 : (4 * T) ^ 2 ≤ (m : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hmT 2
      have h3 : r * (4 * T) ^ 2 ≤ (θ : ℝ) * (m : ℝ) ^ 2 :=
        mul_le_mul hθr hm2 (by positivity) (by positivity)
      have h4 : (n : ℝ) ^ 2 * k * (2 * Real.exp 1 ^ 2) ≤ (n : ℝ) ^ 2 * k * 16 :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have h5 : r * (4 * T) ^ 2 = (n : ℝ) ^ 2 * k * 16 := by rw [← hrT]; ring
      linarith
    have key : ((n.choose m : ℕ) : ℝ) ^ 2 * (k : ℝ) ^ m * 2 ^ m ≤ (θ : ℝ) ^ m := by
      calc ((n.choose m : ℕ) : ℝ) ^ 2 * (k : ℝ) ^ m * 2 ^ m
          ≤ (X ^ m) ^ 2 * (k : ℝ) ^ m * 2 ^ m := by
            gcongr
        _ = (X ^ 2 * k * 2) ^ m := by ring
        _ ≤ (θ : ℝ) ^ m := pow_le_pow_left₀ (by positivity) hbase m
    have keyN : (n.choose m) ^ 2 * k ^ m * 2 ^ m ≤ θ ^ m := by exact_mod_cast key
    rw [← ENNReal.inv_pow, ← ENNReal.inv_pow, ENNReal.le_inv_iff_mul_le]
    calc ((n.choose m : ENNReal)) ^ 2 * (k : ENNReal) ^ m * ((θ : ENNReal) ^ m)⁻¹ * 2 ^ m
        = ((n.choose m : ENNReal) ^ 2 * (k : ENNReal) ^ m * 2 ^ m) / (θ : ENNReal) ^ m := by
          rw [div_eq_mul_inv]; ring
      _ ≤ 1 := ENNReal.div_le_of_le_mul (by rw [one_mul]; exact_mod_cast keyN)
  · have hθlt : (⌈r⌉₊ : ℝ) < r + 1 := Nat.ceil_lt_add_one (by linarith)
    have hm0 : (⌈4 * T⌉₊ : ℝ) < 4 * T + 1 := Nat.ceil_lt_add_one (by linarith)
    have hkθ : (k : ℝ) * ⌈r⌉₊ ≤ k * (r + 1) := mul_le_mul_of_nonneg_left hθlt.le hk0
    have : a ^ 2 * b ^ 2 = T := rfl
    nlinarith

end OnlineColoringKYY.Supplement.Dev.T55.PartR
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T55
open Classical OnlineColoringKYY.Supplement
/-! ### Part R: parameters (real arithmetic) -/
alias params := OnlineColoringKYY.Supplement.Dev.T55.PartR.params

alias trivial_range := OnlineColoringKYY.Supplement.Dev.T55.PartR.trivial_range

end OnlineColoringKYY.Supplement.Dev.T55
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement
open OnlineColoringKYY.Supplement.Dev.T55 in
theorem chk_theorem_5_5 :
    ∃ C : ℝ, 0 < C ∧ ∀ n k : ℕ, ∃ θ : ℕ, 1 ≤ θ ∧
      ∀ (G : SimpleGraph (Fin n)), G.Colorable k →
      ∀ sel : List ℕ → Finset ℕ → ℕ, (∀ c S, S.Nonempty → sel c S ∈ S) →
        expColors (threeLevelRun θ sel G n le_rfl) ≤
          ENNReal.ofReal ((n : ℝ) / 3 + C * (n : ℝ) ^ ((2 : ℝ) / 3) * (k : ℝ) ^ ((2 : ℝ) / 3)) := by
  refine ⟨4, by norm_num, fun n k => ?_⟩
  by_cases hk : 1 ≤ k ∧ k ^ 2 < n
  · obtain ⟨θ, m₀, hθ, htail, harith⟩ := params n k hk.1 hk.2
    refine ⟨θ, hθ, fun G hG sel hsel => ?_⟩
    refine (expColors_le θ hθ sel hsel G hG m₀ htail).trans ?_
    have hR : ((n : ℝ) + 2 * k * θ + m₀ + 2) = ((n + 2 * k * θ + m₀ + 2 : ℕ) : ℝ) := by
      push_cast; ring
    have hE : ((n : ENNReal) + 2 * k * θ + m₀ + 2) = ((n + 2 * k * θ + m₀ + 2 : ℕ) : ENNReal) := by
      push_cast; ring
    rw [hR] at harith
    have h3 := ENNReal.ofReal_le_ofReal harith
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_natCast] at h3
    rw [hE]
    simpa using h3
  · refine ⟨1, le_rfl, fun G hG sel hsel => ?_⟩
    refine (expColors_le_n 1 sel G).trans ?_
    have hkn : n ≤ k ^ 2 := by
      by_cases hk0 : k = 0
      · subst hk0
        rcases Nat.eq_zero_or_pos n with hn | hn
        · simp [hn]
        · exfalso
          obtain ⟨C⟩ := hG
          exact (C ⟨0, hn⟩).elim0
      · simp only [not_and, not_lt] at hk; exact hk (by omega)
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (trivial_range n k hkn)

end OnlineColoringKYY.Supplement
end

theorem solution : type_of% @OnlineColoringKYY.Supplement.chk_theorem_5_5 := @OnlineColoringKYY.Supplement.chk_theorem_5_5
