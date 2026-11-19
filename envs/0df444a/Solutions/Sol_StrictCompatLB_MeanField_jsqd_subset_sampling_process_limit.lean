-- Prove2me | solution 1 for StrictCompatLB.MeanField.jsqd_subset_sampling_process_limit
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-18T08:55:33.483822+00:00
-- url     : https://prove2.me/submissions/22fd71e3-2653-46a7-ba68-11712dbc9b67

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_Model

set_option autoImplicit false

open Filter Topology MeasureTheory
open scoped ENNReal

namespace SC77K3

open StrictCompatLB.MeanField

/-! K3 (JSQ(d) without replacement) part A: deterministic graph facts from proportional sparsity.
`avg_frac`: averaged over dispatchers, the fraction of the neighbourhood inside any `U` is at most
`|U|/N + η` (for large `N`, uniformly in `U`).
`small_deg`: dispatchers of degree at most `K` are a vanishing fraction. -/

lemma frac_le_one {N : ℕ} (A B : Finset (Fin N)) :
    ((A ∩ B).card : ℝ) / (A.card : ℝ) ≤ 1 := by
  rcases Nat.eq_zero_or_pos A.card with h | h
  · simp [h]
  · rw [div_le_one (by exact_mod_cast h)]
    exact_mod_cast Finset.card_le_card Finset.inter_subset_left

lemma frac_nonneg {N : ℕ} (A B : Finset (Fin N)) :
    0 ≤ ((A ∩ B).card : ℝ) / (A.card : ℝ) := by positivity

theorem avg_frac (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N)))
    (hsparse : IsPropSparse M G) (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ U : Finset (Fin N),
      ∑ w : Fin (M N), ((nbrW M G N w ∩ U).card : ℝ) / ((nbrW M G N w).card : ℝ)
        ≤ (M N : ℝ) * ((U.card : ℝ) / (N : ℝ) + η) := by
  obtain ⟨N₀, hN₀⟩ := hsparse (η / 2) (by linarith) (η / 2) (by linarith)
  refine ⟨N₀, fun N hN U => ?_⟩
  have hbad := hN₀ N hN U
  set B := Finset.univ.filter (fun w : Fin (M N) =>
        η / 2 ≤ |((nbrW M G N w ∩ U).card : ℝ) / ((nbrW M G N w).card : ℝ)
              - (U.card : ℝ) / (N : ℝ)|) with hB
  have hU0 : 0 ≤ (U.card : ℝ) / (N : ℝ) := by positivity
  have hterm : ∀ w : Fin (M N),
      ((nbrW M G N w ∩ U).card : ℝ) / ((nbrW M G N w).card : ℝ)
        ≤ ((U.card : ℝ) / (N : ℝ) + η / 2) + (if w ∈ B then 1 else 0) := by
    intro w
    by_cases hw : w ∈ B
    · rw [if_pos hw]
      have := frac_le_one (nbrW M G N w) U
      linarith
    · rw [if_neg hw]
      have hw' : ¬ (η / 2 ≤ |((nbrW M G N w ∩ U).card : ℝ) / ((nbrW M G N w).card : ℝ)
              - (U.card : ℝ) / (N : ℝ)|) := by
        intro h; exact hw (by rw [hB]; simp [h])
      push_neg at hw'
      have := (abs_lt.mp hw').2
      linarith
  calc ∑ w : Fin (M N), ((nbrW M G N w ∩ U).card : ℝ) / ((nbrW M G N w).card : ℝ)
      ≤ ∑ w : Fin (M N), (((U.card : ℝ) / (N : ℝ) + η / 2) + (if w ∈ B then 1 else 0)) :=
        Finset.sum_le_sum (fun w _ => hterm w)
    _ = (M N : ℝ) * ((U.card : ℝ) / (N : ℝ) + η / 2) + (B.card : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, Finset.sum_boole]
        simp
    _ ≤ (M N : ℝ) * ((U.card : ℝ) / (N : ℝ) + η / 2) + η / 2 * (M N : ℝ) := by
        linarith
    _ = (M N : ℝ) * ((U.card : ℝ) / (N : ℝ) + η) := by ring

/-- Dispatchers of degree at most `K` form a vanishing fraction. -/
theorem small_deg (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N)))
    (hsparse : IsPropSparse M G) (K : ℕ) (hK : 1 ≤ K) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (((Finset.univ.filter (fun w : Fin (M N) => (nbrW M G N w).card ≤ K)).card : ℕ) : ℝ)
        ≤ δ * (M N : ℝ) := by
  set L : ℕ := 2 * K + 2 with hL
  have hLpos : (0 : ℝ) < L := by positivity
  obtain ⟨N₁, hN₁⟩ := hsparse (1 / (2 * (L : ℝ))) (by positivity) δ hδ
  refine ⟨max N₁ (2 * L), fun N hN => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : 2 * L ≤ N := le_trans (le_max_right _ _) hN
  set m : ℕ := N / L with hm
  have hmN : m ≤ N := Nat.div_le_self N L
  obtain ⟨U, -, hUc⟩ : ∃ U ⊆ (Finset.univ : Finset (Fin N)), U.card = m := by
    apply Finset.exists_subset_card_eq
    simpa using hmN
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  -- bounds on m / N
  have hmL : (m : ℝ) * L ≤ N := by
    have := Nat.div_mul_le_self N L
    exact_mod_cast this
  have hmL2 : (N : ℝ) < ((m : ℝ) + 1) * L := by
    have h1 := Nat.lt_div_mul_add (a := N) (b := L) (by omega)
    have : N < (m + 1) * L := by
      rw [hm]; nlinarith [h1]
    exact_mod_cast this
  have hup : (m : ℝ) / N ≤ 1 / L := by
    rw [div_le_div_iff₀ hNpos hLpos]; linarith
  have hlow : 1 / (2 * (L : ℝ)) ≤ (m : ℝ) / N := by
    rw [div_le_div_iff₀ (by positivity) hNpos]
    have : (2 * L : ℝ) ≤ N := by exact_mod_cast hN2
    nlinarith
  have hsub : (Finset.univ.filter (fun w : Fin (M N) => (nbrW M G N w).card ≤ K)) ⊆
      Finset.univ.filter (fun w : Fin (M N) =>
        1 / (2 * (L : ℝ)) ≤ |((nbrW M G N w ∩ U).card : ℝ) / ((nbrW M G N w).card : ℝ)
              - (U.card : ℝ) / (N : ℝ)|) := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    rw [hUc]
    set n := (nbrW M G N w).card
    set j := (nbrW M G N w ∩ U).card
    rcases Nat.eq_zero_or_pos j with hj | hj
    · rw [hj]; simp only [Nat.cast_zero, zero_div, zero_sub, abs_neg]
      rw [abs_of_nonneg (by positivity)]; exact hlow
    · have hn : 1 ≤ n := le_trans hj (Finset.card_le_card Finset.inter_subset_left)
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      have hfrac : 1 / (K : ℝ) ≤ (j : ℝ) / n := by
        rw [div_le_div_iff₀ (by exact_mod_cast hK) hnpos]
        have : (n : ℝ) ≤ K := by exact_mod_cast hw
        have : (1 : ℝ) ≤ j := by exact_mod_cast hj
        nlinarith
      have hKL : 2 / (L : ℝ) ≤ 1 / (K : ℝ) := by
        rw [div_le_div_iff₀ hLpos (by exact_mod_cast hK)]
        have : (L : ℝ) = 2 * K + 2 := by rw [hL]; push_cast; ring
        rw [this]; linarith
      have hpos : 1 / (L : ℝ) ≤ (j : ℝ) / n - (m : ℝ) / N := by
        have : 2 / (L : ℝ) = 1 / L + 1 / L := by ring
        linarith
      rw [abs_of_nonneg (by linarith [show (0:ℝ) < 1 / L by positivity])]
      have : 1 / (2 * (L : ℝ)) ≤ 1 / L := by
        rw [div_le_div_iff₀ (by positivity) hLpos]; linarith
      linarith
  calc (((Finset.univ.filter (fun w : Fin (M N) => (nbrW M G N w).card ≤ K)).card : ℕ) : ℝ)
      ≤ (((Finset.univ.filter (fun w : Fin (M N) =>
        1 / (2 * (L : ℝ)) ≤ |((nbrW M G N w ∩ U).card : ℝ) / ((nbrW M G N w).card : ℝ)
              - (U.card : ℝ) / (N : ℝ)|)).card : ℕ) : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ δ * (M N : ℝ) := hN₁ N hN1 U

/-! Part C: `piRoute (jsqdAssign d)` at two states differing on `U` (TV bound `C |𝒩_w ∩ U| / |𝒩_w|`). -/

/-- `S d a b = ∑_{k<d} a^k b^(d-1-k)`, so `a^d - b^d = (a - b) S d a b`. -/
noncomputable def S (d : ℕ) (a b : ℝ) : ℝ := ∑ k ∈ Finset.range d, a ^ k * b ^ (d - 1 - k)

lemma S_mul (d : ℕ) (a b : ℝ) : a ^ d - b ^ d = (a - b) * S d a b := by
  unfold S; rw [mul_comm]; exact (geom_sum₂_mul a b d).symm

lemma S_nonneg (d : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ S d a b :=
  Finset.sum_nonneg (fun k _ => by positivity)

lemma S_le (d : ℕ) (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    S d a b ≤ d := by
  unfold S
  calc ∑ k ∈ Finset.range d, a ^ k * b ^ (d - 1 - k) ≤ ∑ _k ∈ Finset.range d, (1 : ℝ) :=
        Finset.sum_le_sum (fun k _ => mul_le_one₀ (pow_le_one₀ ha ha1) (by positivity)
          (pow_le_one₀ hb hb1))
    _ = d := by simp

lemma pow_sub_le (k : ℕ) (a a' : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ha' : 0 ≤ a') (ha1' : a' ≤ 1) :
    |a ^ k - a' ^ k| ≤ k * |a - a'| := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : a ^ (k + 1) - a' ^ (k + 1) = a * (a ^ k - a' ^ k) + a' ^ k * (a - a') := by ring
    rw [e]
    calc |a * (a ^ k - a' ^ k) + a' ^ k * (a - a')|
        ≤ |a * (a ^ k - a' ^ k)| + |a' ^ k * (a - a')| := abs_add_le _ _
      _ = a * |a ^ k - a' ^ k| + a' ^ k * |a - a'| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg (by positivity : 0 ≤ a' ^ k)]
      _ ≤ 1 * (k * |a - a'|) + 1 * |a - a'| := by
          gcongr
          · exact pow_le_one₀ ha' ha1'
      _ = ((k + 1 : ℕ) : ℝ) * |a - a'| := by push_cast; ring

lemma S_lip (d : ℕ) (a b a' b' : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (ha' : 0 ≤ a') (ha1' : a' ≤ 1) (hb' : 0 ≤ b') (hb1' : b' ≤ 1) :
    |S d a b - S d a' b'| ≤ (d : ℝ) ^ 2 * (|a - a'| + |b - b'|) := by
  unfold S
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ k ∈ Finset.range d, |a ^ k * b ^ (d - 1 - k) - a' ^ k * b' ^ (d - 1 - k)|
      ≤ d * (|a - a'| + |b - b'|) := by
    intro k hk
    have hkd : k ≤ d := (Finset.mem_range.mp hk).le
    have e : a ^ k * b ^ (d - 1 - k) - a' ^ k * b' ^ (d - 1 - k)
        = (a ^ k - a' ^ k) * b ^ (d - 1 - k) + a' ^ k * (b ^ (d - 1 - k) - b' ^ (d - 1 - k)) := by
      ring
    rw [e]
    have h1 := pow_sub_le k a a' ha ha1 ha' ha1'
    have h2 := pow_sub_le (d - 1 - k) b b' hb hb1 hb' hb1'
    have hk1 : (k : ℝ) ≤ d := by exact_mod_cast hkd
    have hk2 : ((d - 1 - k : ℕ) : ℝ) ≤ d := by exact_mod_cast (by omega : d - 1 - k ≤ d)
    have hbk : b ^ (d - 1 - k) ≤ 1 := pow_le_one₀ hb hb1
    have hak : a' ^ k ≤ 1 := pow_le_one₀ ha' ha1'
    calc |(a ^ k - a' ^ k) * b ^ (d - 1 - k) + a' ^ k * (b ^ (d - 1 - k) - b' ^ (d - 1 - k))|
        ≤ |a ^ k - a' ^ k| * b ^ (d - 1 - k) + a' ^ k * |b ^ (d - 1 - k) - b' ^ (d - 1 - k)| := by
          refine (abs_add_le _ _).trans (le_of_eq ?_)
          rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ b ^ (d - 1 - k)),
            abs_of_nonneg (by positivity : 0 ≤ a' ^ k)]
      _ ≤ |a ^ k - a' ^ k| * 1 + 1 * |b ^ (d - 1 - k) - b' ^ (d - 1 - k)| := by
          gcongr
      _ ≤ d * |a - a'| + d * |b - b'| := by
          have := abs_nonneg (a - a'); have := abs_nonneg (b - b')
          nlinarith
      _ = d * (|a - a'| + |b - b'|) := by ring
  calc |∑ k ∈ Finset.range d, (a ^ k * b ^ (d - 1 - k) - a' ^ k * b' ^ (d - 1 - k))|
      ≤ ∑ k ∈ Finset.range d, |a ^ k * b ^ (d - 1 - k) - a' ^ k * b' ^ (d - 1 - k)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range d, (d : ℝ) * (|a - a'| + |b - b'|) := Finset.sum_le_sum hterm
    _ = (d : ℝ) ^ 2 * (|a - a'| + |b - b'|) := by simp; ring

/-- Count of neighbours of `w` with queue at least `i`. -/
def Acnt (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ) (z : Fin N → ℕ)
    (w : Fin (M N)) (i : ℕ) : ℕ :=
  ((nbrW M G N w).filter (fun v => i ≤ z v)).card

lemma tail_leqd (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ)
    (z : Fin N → ℕ) (w : Fin (M N)) (i : ℕ) :
    tailOf (leqd M G N z w) i = (Acnt M G N z w i : ℝ) / ((nbrW M G N w).card : ℝ) := by
  set B : ℕ := ∑ v, z v + 1 with hB
  have hzB : ∀ v, z v < B := fun v => by
    have := Finset.single_le_sum (f := z) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
    omega
  unfold tailOf
  rw [tsum_eq_sum (s := Finset.range B)]
  · unfold leqd Acnt
    have hcount : ((nbrW M G N w).filter (fun v => i ≤ z v)).card
        = ∑ j ∈ Finset.range B,
            (if i ≤ j then ((nbrW M G N w).filter (fun v => z v = j)).card else 0) := by
      rw [Finset.card_eq_sum_card_fiberwise (f := z) (t := Finset.range B)]
      · apply Finset.sum_congr rfl
        intro j _
        split_ifs with hij
        · congr 1; ext v; simp only [Finset.mem_filter]
          constructor
          · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
          · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3 ▸ hij⟩, h3⟩
        · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro v hv; simp only [Finset.mem_filter] at hv; omega
      · intro v _; exact Finset.mem_range.mpr (hzB v)
    rw [hcount]; push_cast
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _; split_ifs <;> simp
  · intro j hj
    have hj' : B ≤ j := by simpa using hj
    split_ifs
    · unfold leqd
      rw [show ((nbrW M G N w).filter (fun v => z v = j)) = ∅ by
        rw [Finset.filter_eq_empty_iff]; intro v _ h; have := hzB v; omega]
      simp
    · rfl

lemma Acnt_le (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ)
    (z : Fin N → ℕ) (w : Fin (M N)) (i : ℕ) : Acnt M G N z w i ≤ (nbrW M G N w).card :=
  Finset.card_filter_le _ _

lemma Acnt_sub (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ)
    (z : Fin N → ℕ) (w : Fin (M N)) (i : ℕ) :
    (Acnt M G N z w i : ℝ) - Acnt M G N z w (i + 1)
      = (((nbrW M G N w).filter (fun u => z u = i)).card : ℝ) := by
  unfold Acnt
  have e : (nbrW M G N w).filter (fun v => i ≤ z v)
      = (nbrW M G N w).filter (fun v => i + 1 ≤ z v) ∪ (nbrW M G N w).filter (fun v => z v = i) := by
    ext v
    simp only [Finset.mem_union, Finset.mem_filter]
    by_cases hv : v ∈ nbrW M G N w
    · simp only [hv, true_and]; omega
    · simp [hv]
  have hd : Disjoint ((nbrW M G N w).filter (fun v => i + 1 ≤ z v))
      ((nbrW M G N w).filter (fun v => z v = i)) :=
    Finset.disjoint_filter.mpr (fun v _ h1 h2 => by omega)
  rw [e]
  first
    | rw [Finset.card_union_of_disjoint hd]
    | rw [Finset.card_union_eq_card_add_card.mpr hd]
  push_cast; ring

/-- Closed form: `piRoute (jsqdAssign d)` at a neighbour `v` equals `S(A_{z_v}/n, A_{z_v+1}/n)/n`. -/
lemma piRoute_jsqd (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N d : ℕ)
    (z : Fin N → ℕ) (w : Fin (M N)) (v : Fin N) (hv : v ∈ nbrW M G N w) :
    piRoute M G N (jsqdAssign d) w z v
      = S d ((Acnt M G N z w (z v) : ℝ) / (nbrW M G N w).card)
            ((Acnt M G N z w (z v + 1) : ℝ) / (nbrW M G N w).card)
          / (nbrW M G N w).card := by
  unfold piRoute jsqdAssign
  rw [if_pos hv, tail_leqd, tail_leqd, S_mul]
  have hm : 1 ≤ ((nbrW M G N w).filter (fun u => z u = z v)).card :=
    Finset.card_pos.mpr ⟨v, by simp [hv]⟩
  have hn : 1 ≤ (nbrW M G N w).card := Finset.card_pos.mpr ⟨v, hv⟩
  have hmR : (0 : ℝ) < ((nbrW M G N w).filter (fun u => z u = z v)).card := by exact_mod_cast hm
  have hnR : (0 : ℝ) < (nbrW M G N w).card := by exact_mod_cast hn
  rw [← sub_div, Acnt_sub]
  field_simp

lemma Acnt_diff (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ)
    (z y : Fin N → ℕ) (w : Fin (M N)) (i : ℕ) :
    |(Acnt M G N z w i : ℝ) - Acnt M G N y w i|
      ≤ ((nbrW M G N w ∩ Finset.univ.filter (fun v => z v ≠ y v)).card : ℝ) := by
  have key : ∀ z y : Fin N → ℕ, (Acnt M G N z w i : ℝ) ≤ Acnt M G N y w i
      + ((nbrW M G N w ∩ Finset.univ.filter (fun v => z v ≠ y v)).card : ℝ) := by
    intro z y
    unfold Acnt
    have hsub : (nbrW M G N w).filter (fun v => i ≤ z v) ⊆
        (nbrW M G N w).filter (fun v => i ≤ y v) ∪
          (nbrW M G N w ∩ Finset.univ.filter (fun v => z v ≠ y v)) := by
      intro v hv
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_inter, Finset.mem_univ,
        true_and] at hv ⊢
      by_cases h : z v = y v
      · left; exact ⟨hv.1, h ▸ hv.2⟩
      · right; exact ⟨hv.1, h⟩
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    exact_mod_cast this
  have h1 := key z y
  have h2 := key y z
  have e : Finset.univ.filter (fun v => y v ≠ z v) = Finset.univ.filter (fun v => z v ≠ y v) := by
    ext v; simp [ne_comm]
  rw [e] at h2
  rw [abs_le]; constructor <;> linarith

/-- K3c: total variation between `piRoute (jsqdAssign d)` at two states, bounded by the fraction
of `𝒩_w` where they differ. -/
theorem tv_piRoute (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N d : ℕ)
    (z y : Fin N → ℕ) (w : Fin (M N)) :
    ∑ v : Fin N, |piRoute M G N (jsqdAssign d) w z v - piRoute M G N (jsqdAssign d) w y v|
      ≤ (2 * (d : ℝ) ^ 2 + 2 * d) *
        (((nbrW M G N w ∩ Finset.univ.filter (fun v => z v ≠ y v)).card : ℝ)
          / (nbrW M G N w).card) := by
  set Nw := nbrW M G N w
  set U := Finset.univ.filter (fun v : Fin N => z v ≠ y v)
  set n : ℝ := (Nw.card : ℝ)
  set u : ℝ := ((Nw ∩ U).card : ℝ)
  have hoff : ∀ v, v ∉ Nw →
      |piRoute M G N (jsqdAssign d) w z v - piRoute M G N (jsqdAssign d) w y v| = 0 := by
    intro v hv; unfold piRoute; simp [Nw, hv]
  rw [← Finset.sum_subset (Finset.subset_univ Nw) (fun v _ hv => hoff v hv)]
  rcases Nat.eq_zero_or_pos Nw.card with h0 | hpos
  · rw [Finset.card_eq_zero.mp h0]; simp only [Finset.sum_empty]; positivity
  have hnR : (0 : ℝ) < n := by simp only [n]; exact_mod_cast hpos
  have hu0 : 0 ≤ u := by positivity
  have hfr : ∀ (x : Fin N → ℕ) (i : ℕ), 0 ≤ (Acnt M G N x w i : ℝ) / n ∧
      (Acnt M G N x w i : ℝ) / n ≤ 1 := by
    intro x i
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hnR]; simp only [n, Nw]; exact_mod_cast Acnt_le M G N x w i
  have hbound : ∀ v ∈ Nw,
      |piRoute M G N (jsqdAssign d) w z v - piRoute M G N (jsqdAssign d) w y v|
        ≤ (if v ∈ U then 2 * (d : ℝ) / n else 0) + 2 * (d : ℝ) ^ 2 * u / (n * n) := by
    intro v hv
    rw [piRoute_jsqd M G N d z w v hv, piRoute_jsqd M G N d y w v hv]
    rw [← sub_div, abs_div, abs_of_pos hnR]
    by_cases hU : v ∈ U
    · rw [if_pos hU]
      have hz1 := S_le d _ _ (hfr z (z v)).1 (hfr z (z v)).2 (hfr z (z v + 1)).1 (hfr z (z v + 1)).2
      have hz0 := S_nonneg d _ _ (hfr z (z v)).1 (hfr z (z v + 1)).1
      have hy1 := S_le d _ _ (hfr y (y v)).1 (hfr y (y v)).2 (hfr y (y v + 1)).1 (hfr y (y v + 1)).2
      have hy0 := S_nonneg d _ _ (hfr y (y v)).1 (hfr y (y v + 1)).1
      have habs : |S d ((Acnt M G N z w (z v) : ℝ) / n) ((Acnt M G N z w (z v + 1) : ℝ) / n) -
          S d ((Acnt M G N y w (y v) : ℝ) / n) ((Acnt M G N y w (y v + 1) : ℝ) / n)| ≤ 2 * d := by
        rw [abs_le]; constructor <;> linarith
      have : 0 ≤ 2 * (d : ℝ) ^ 2 * u / (n * n) := by positivity
      have h2 : |S d ((Acnt M G N z w (z v) : ℝ) / n) ((Acnt M G N z w (z v + 1) : ℝ) / n) -
          S d ((Acnt M G N y w (y v) : ℝ) / n) ((Acnt M G N y w (y v + 1) : ℝ) / n)| / n
            ≤ 2 * d / n := div_le_div_of_nonneg_right habs hnR.le
      linarith
    · rw [if_neg hU, zero_add]
      have hzy : z v = y v := by
        by_contra h; exact hU (by simp [U, h])
      rw [← hzy]
      have hl := S_lip d _ _ _ _ (hfr z (z v)).1 (hfr z (z v)).2 (hfr z (z v + 1)).1
        (hfr z (z v + 1)).2 (hfr y (z v)).1 (hfr y (z v)).2 (hfr y (z v + 1)).1 (hfr y (z v + 1)).2
      have ha : |(Acnt M G N z w (z v) : ℝ) / n - (Acnt M G N y w (z v) : ℝ) / n| ≤ u / n := by
        rw [← sub_div, abs_div, abs_of_pos hnR]
        exact div_le_div_of_nonneg_right (Acnt_diff M G N z y w (z v)) hnR.le
      have hb : |(Acnt M G N z w (z v + 1) : ℝ) / n - (Acnt M G N y w (z v + 1) : ℝ) / n|
          ≤ u / n := by
        rw [← sub_div, abs_div, abs_of_pos hnR]
        exact div_le_div_of_nonneg_right (Acnt_diff M G N z y w (z v + 1)) hnR.le
      have hS : |S d ((Acnt M G N z w (z v) : ℝ) / n) ((Acnt M G N z w (z v + 1) : ℝ) / n) -
          S d ((Acnt M G N y w (z v) : ℝ) / n) ((Acnt M G N y w (z v + 1) : ℝ) / n)|
            ≤ 2 * (d : ℝ) ^ 2 * u / n := by
        have : (d : ℝ) ^ 2 * (u / n + u / n) = 2 * (d : ℝ) ^ 2 * u / n := by ring
        rw [← this]
        exact hl.trans (by gcongr)
      calc _ ≤ 2 * (d : ℝ) ^ 2 * u / n / n := div_le_div_of_nonneg_right hS hnR.le
        _ = 2 * (d : ℝ) ^ 2 * u / (n * n) := by rw [div_div]
  calc ∑ v ∈ Nw, |piRoute M G N (jsqdAssign d) w z v - piRoute M G N (jsqdAssign d) w y v|
      ≤ ∑ v ∈ Nw, ((if v ∈ U then 2 * (d : ℝ) / n else 0) + 2 * (d : ℝ) ^ 2 * u / (n * n)) :=
        Finset.sum_le_sum hbound
    _ = 2 * (d : ℝ) / n * u + n * (2 * (d : ℝ) ^ 2 * u / (n * n)) := by
        rw [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero,
          Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul,
          Finset.filter_mem_eq_inter]
        simp only [u, n]; ring
    _ = (2 * (d : ℝ) ^ 2 + 2 * d) * (u / n) := by field_simp; ring

end SC77K3

set_option autoImplicit false

open Filter Topology MeasureTheory
open scoped ENNReal

namespace SC77K3A

open StrictCompatLB.MeanField

/-! K3a: total variation between JSQ(d) without replacement (`jsqdRoute`) and the generic policy
with the JSQ(d) assignment function (`piRoute (jsqdAssign d)`, i.e. d draws with replacement):
`∑_v |jsqdRoute - piRoute| ≤ 2 d^3 / |𝒩_w|`. -/

/-! ### Numeric part -/

noncomputable def Fq (n k a : ℕ) : ℝ := (a.choose k : ℝ) / (n.choose k : ℝ)
noncomputable def Gq (n d a : ℕ) : ℝ := ((a : ℝ) / n) ^ d

lemma pow_sub_pow_le_c (e : ℕ) (x y c : ℝ) (hy : 0 ≤ y) (hyx : y ≤ x) (hxc : x ≤ c) :
    x ^ e - y ^ e ≤ e * c ^ (e - 1) * (x - y) := by
  induction e with
  | zero => simp
  | succ e ih =>
    have hx : 0 ≤ x := hy.trans hyx
    have hc : 0 ≤ c := hx.trans hxc
    have h1 : x ^ (e+1) - y ^ (e+1) = x * (x ^ e - y ^ e) + y ^ e * (x - y) := by ring
    have h2 : x * (x ^ e - y ^ e) ≤ c * (e * c ^ (e - 1) * (x - y)) :=
      mul_le_mul hxc ih (sub_nonneg.mpr (pow_le_pow_left₀ hy hyx e)) hc
    have h3 : y ^ e * (x - y) ≤ c ^ e * (x - y) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hy (hyx.trans hxc) e) (sub_nonneg.mpr hyx)
    have h4 : c * (e * c ^ (e - 1)) = e * c ^ e := by
      rcases Nat.eq_zero_or_pos e with he | he
      · subst he; simp
      · rw [mul_left_comm, mul_pow_sub_one (Nat.pos_iff_ne_zero.mp he)]
    have h5 : c * (e * c ^ (e - 1) * (x - y)) = e * c ^ e * (x - y) := by
      rw [← h4]; ring
    simp only [Nat.add_sub_cancel]
    push_cast
    nlinarith [h1, h2, h3, h5]

lemma abs_eq_two_pos (δ : ℝ) : |δ| = δ + 2 * max (-δ) 0 := by
  rcases le_total 0 δ with h | h
  · rw [abs_of_nonneg h, max_eq_right (by linarith)]; ring
  · rw [abs_of_nonpos h, max_eq_left (by linarith)]; ring

lemma dF_nonneg (n k a : ℕ) : 0 ≤ Fq n k (a+1) - Fq n k a := by
  unfold Fq; rw [← sub_div]
  apply div_nonneg _ (Nat.cast_nonneg _)
  rw [sub_nonneg]; exact_mod_cast Nat.choose_le_choose k (Nat.le_succ a)

lemma dG_nonneg (n d a : ℕ) : 0 ≤ Gq n d (a+1) - Gq n d a := by
  unfold Gq; rw [sub_nonneg]
  apply pow_le_pow_left₀ (by positivity)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  push_cast; linarith

lemma sumF (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    ∑ a ∈ Finset.range n, (Fq n k (a+1) - Fq n k a) = 1 := by
  rw [Finset.sum_range_sub]
  unfold Fq
  have hpos : (0 : ℝ) < (n.choose k : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos hkn)
  rw [div_self hpos.ne', Nat.choose_eq_zero_of_lt (by omega : 0 < k)]
  simp

lemma sumG (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) :
    ∑ a ∈ Finset.range n, (Gq n d (a+1) - Gq n d a) = 1 := by
  rw [Finset.sum_range_sub]
  unfold Gq
  have hnR : (n : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ n := by exact_mod_cast hn
                               linarith
  rw [div_self hnR]
  simp [zero_pow (by omega : d ≠ 0)]

theorem tv_num (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) :
    ∑ a ∈ Finset.range n,
      |(Fq n (min d n) (a+1) - Gq n d (a+1)) - (Fq n (min d n) a - Gq n d a)|
        ≤ 2 * (d : ℝ) ^ 3 / n := by
  set k := min d n with hk
  have hk1 : 1 ≤ k := le_min hd hn
  have hkn : k ≤ n := min_le_right _ _
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have e1 : ∀ a, (Fq n k (a+1) - Gq n d (a+1)) - (Fq n k a - Gq n d a)
      = (Fq n k (a+1) - Fq n k a) - (Gq n d (a+1) - Gq n d a) := fun a => by ring
  simp_rw [e1, abs_eq_two_pos]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, sumF n k hk1 hkn, sumG n d hn hd,
    ← Finset.mul_sum]
  by_cases hdn : d ≤ n
  · have hkd : k = d := min_eq_left hdn
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    set β : ℝ := (e + 1) * ((e : ℝ) ^ 2 * (n : ℝ) ^ (e - 1)) / (n : ℝ) ^ (e + 1) with hβ
    have hterm : ∀ a ∈ Finset.range n,
        max (-((Fq n k (a+1) - Fq n k a) - (Gq n (e+1) (a+1) - Gq n (e+1) a))) 0 ≤ β := by
      intro a ha
      have ha' : a + 1 ≤ n := Finset.mem_range.mp ha
      apply max_le _ (by positivity)
      rw [hkd]
      set y : ℝ := ((a + 1 - e : ℕ) : ℝ) with hy
      have hF : (e + 1 : ℝ) * y ^ e / (n : ℝ) ^ (e + 1)
          ≤ Fq n (e+1) (a+1) - Fq n (e+1) a := by
        unfold Fq
        rw [← sub_div, Nat.choose_succ_succ', Nat.cast_add, add_sub_cancel_right]
        have h3 : (0 : ℝ) < (n.choose (e+1) : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos hdn)
        have hf : (0 : ℝ) < (e.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos e
        have h1 : y ^ e ≤ (a.choose e : ℝ) * (e.factorial : ℝ) := by
          have := Nat.pow_le_choose (α := ℝ) e a
          rw [div_le_iff₀ hf] at this
          simpa [hy] using this
        have h2 : (n.choose (e+1) : ℝ) * ((e + 1 : ℝ) * (e.factorial : ℝ)) ≤ (n : ℝ) ^ (e+1) := by
          have := Nat.choose_le_pow_div (α := ℝ) (e+1) n
          rw [Nat.factorial_succ] at this
          push_cast at this
          rw [le_div_iff₀ (by positivity)] at this
          linarith
        rw [div_le_div_iff₀ (by positivity) h3]
        have hy0 : 0 ≤ y := by positivity
        calc (e + 1 : ℝ) * y ^ e * (n.choose (e+1) : ℝ)
            ≤ (e + 1 : ℝ) * ((a.choose e : ℝ) * (e.factorial : ℝ)) * (n.choose (e+1) : ℝ) := by
              gcongr
          _ = (a.choose e : ℝ) * ((n.choose (e+1) : ℝ) * ((e + 1 : ℝ) * (e.factorial : ℝ))) := by
              ring
          _ ≤ (a.choose e : ℝ) * (n : ℝ) ^ (e+1) := by gcongr
      have hG : Gq n (e+1) (a+1) - Gq n (e+1) a ≤ (e + 1 : ℝ) * ((a : ℝ) + 1) ^ e / (n : ℝ) ^ (e + 1) := by
        unfold Gq
        rw [div_pow, div_pow, ← sub_div]
        apply div_le_div_of_nonneg_right _ (by positivity)
        have := pow_sub_pow_le_c (e+1) ((a : ℝ) + 1) a ((a : ℝ) + 1) (Nat.cast_nonneg a)
          (by linarith) le_rfl
        push_cast
        simpa using this
      have hP : ((a : ℝ) + 1) ^ e - y ^ e ≤ (e : ℝ) ^ 2 * (n : ℝ) ^ (e - 1) := by
        have hy0 : 0 ≤ y := by positivity
        have hya : y ≤ (a : ℝ) + 1 := by
          rw [hy]; exact_mod_cast Nat.sub_le (a + 1) e
        have han : (a : ℝ) + 1 ≤ n := by exact_mod_cast ha'
        have hdiff : (a : ℝ) + 1 - y ≤ e := by
          have : a + 1 ≤ (a + 1 - e) + e := by omega
          have : ((a : ℝ) + 1) ≤ y + e := by rw [hy]; exact_mod_cast this
          linarith
        have := pow_sub_pow_le_c e ((a : ℝ) + 1) y n hy0 hya han
        have hc : 0 ≤ (e : ℝ) * (n : ℝ) ^ (e - 1) := by positivity
        calc ((a : ℝ) + 1) ^ e - y ^ e ≤ (e : ℝ) * (n : ℝ) ^ (e - 1) * ((a : ℝ) + 1 - y) := this
          _ ≤ (e : ℝ) * (n : ℝ) ^ (e - 1) * e := mul_le_mul_of_nonneg_left hdiff hc
          _ = (e : ℝ) ^ 2 * (n : ℝ) ^ (e - 1) := by ring
      have hfin : (e + 1 : ℝ) * ((a : ℝ) + 1) ^ e / (n : ℝ) ^ (e + 1)
          - (e + 1 : ℝ) * y ^ e / (n : ℝ) ^ (e + 1) ≤ β := by
        rw [← sub_div, ← mul_sub, hβ]
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hP (by positivity)
      push_cast
      linarith
    have hs := Finset.sum_le_sum hterm
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
    have hnb : (n : ℝ) * β = (e + 1) * (e : ℝ) ^ 2 / n := by
      rw [hβ]
      cases e with
      | zero => simp
      | succ f =>
        simp only [Nat.add_sub_cancel]
        field_simp
        ring
    have hlast : (e + 1 : ℝ) * (e : ℝ) ^ 2 / n ≤ ((e + 1 : ℕ) : ℝ) ^ 3 / n := by
      apply div_le_div_of_nonneg_right _ hnR.le
      push_cast
      have he : (0 : ℝ) ≤ e := Nat.cast_nonneg e
      nlinarith [sq_nonneg (e : ℝ)]
    have : (1 : ℝ) - 1 + 2 * ∑ a ∈ Finset.range n,
        max (-((Fq n k (a+1) - Fq n k a) - (Gq n (e+1) (a+1) - Gq n (e+1) a))) 0
          ≤ 2 * ((e + 1 : ℕ) : ℝ) ^ 3 / n := by
      rw [mul_div_assoc]
      nlinarith [hs, hnb, hlast]
    exact this
  · rw [not_le] at hdn
    have hterm : ∀ a ∈ Finset.range n,
        max (-((Fq n k (a+1) - Fq n k a) - (Gq n d (a+1) - Gq n d a))) 0
          ≤ Gq n d (a+1) - Gq n d a := by
      intro a _
      exact max_le (by linarith [dF_nonneg n k a]) (dG_nonneg n d a)
    have hs := Finset.sum_le_sum hterm
    rw [sumG n d hn hd] at hs
    have h2 : (2 : ℝ) ≤ 2 * (d : ℝ) ^ 3 / n := by
      rw [le_div_iff₀ hnR]
      have h1 : (n : ℝ) ≤ d := by exact_mod_cast hdn.le
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
      nlinarith [mul_le_mul hd1 hd1 zero_le_one (by linarith : (0:ℝ) ≤ d)]
    linarith

/-! ### Chain (telescoping along the level counts) -/

lemma tele_Ico (H : ℕ → ℝ) (m n : ℕ) (h : m ≤ n) :
    |H n - H m| ≤ ∑ a ∈ Finset.Ico m n, |H (a+1) - H a| := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hs : ∑ k ∈ Finset.range (n - m), (H (m + k + 1) - H (m + k)) = H n - H m := by
    have := Finset.sum_range_sub (fun k => H (m + k)) (n - m)
    simp only [add_zero] at this
    rw [Nat.add_sub_cancel' h] at this
    exact this
  rw [← hs]
  exact Finset.abs_sum_le_sum_abs _ _

lemma chain (H : ℕ → ℝ) (A : ℕ → ℕ) (hA : Antitone A) (B : ℕ) :
    ∑ i ∈ Finset.range B, |H (A i) - H (A (i+1))|
      ≤ ∑ a ∈ Finset.Ico (A B) (A 0), |H (a+1) - H a| := by
  induction B with
  | zero => simp
  | succ B ih =>
    rw [Finset.sum_range_succ]
    have hle : A (B+1) ≤ A B := hA (Nat.le_succ B)
    have hle0 : A B ≤ A 0 := hA (Nat.zero_le B)
    have h1 := tele_Ico H (A (B+1)) (A B) hle
    rw [← Finset.sum_Ico_consecutive _ hle hle0]
    linarith

/-! ### Graph part -/

def Acnt (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ) (z : Fin N → ℕ)
    (w : Fin (M N)) (i : ℕ) : ℕ :=
  ((nbrW M G N w).filter (fun v => i ≤ z v)).card

lemma tail_leqd (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ)
    (z : Fin N → ℕ) (w : Fin (M N)) (i : ℕ) :
    tailOf (leqd M G N z w) i = (Acnt M G N z w i : ℝ) / ((nbrW M G N w).card : ℝ) := by
  set B : ℕ := ∑ v, z v + 1 with hB
  have hzB : ∀ v, z v < B := fun v => by
    have := Finset.single_le_sum (f := z) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
    omega
  unfold tailOf
  rw [tsum_eq_sum (s := Finset.range B)]
  · unfold leqd Acnt
    have hcount : ((nbrW M G N w).filter (fun v => i ≤ z v)).card
        = ∑ j ∈ Finset.range B,
            (if i ≤ j then ((nbrW M G N w).filter (fun v => z v = j)).card else 0) := by
      rw [Finset.card_eq_sum_card_fiberwise (f := z) (t := Finset.range B)]
      · apply Finset.sum_congr rfl
        intro j _
        split_ifs with hij
        · congr 1; ext v; simp only [Finset.mem_filter]
          constructor
          · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
          · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3 ▸ hij⟩, h3⟩
        · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro v hv; simp only [Finset.mem_filter] at hv; omega
      · intro v _; exact Finset.mem_range.mpr (hzB v)
    rw [hcount]; push_cast
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _; split_ifs <;> simp
  · intro j hj
    have hj' : B ≤ j := by simpa using hj
    split_ifs
    · unfold leqd
      rw [show ((nbrW M G N w).filter (fun v => z v = j)) = ∅ by
        rw [Finset.filter_eq_empty_iff]; intro v _ h; have := hzB v; omega]
      simp
    · rfl

lemma Acnt_le (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ)
    (z : Fin N → ℕ) (w : Fin (M N)) (i : ℕ) : Acnt M G N z w i ≤ (nbrW M G N w).card :=
  Finset.card_filter_le _ _

lemma Acnt_anti (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ)
    (z : Fin N → ℕ) (w : Fin (M N)) : Antitone (fun i => Acnt M G N z w i) := by
  intro i j hij
  apply Finset.card_le_card
  intro v hv
  simp only [Finset.mem_filter] at hv ⊢
  exact ⟨hv.1, le_trans hij hv.2⟩

lemma argmin_map {N : ℕ} (σ : Equiv.Perm (Fin N)) (z : Fin N → ℕ) (hz : ∀ u, z (σ u) = z u)
    (U : Finset (Fin N)) :
    argminSet (U.map σ.toEmbedding) z = (argminSet U z).map σ.toEmbedding := by
  ext x
  constructor
  · intro hx
    rw [argminSet, Finset.mem_filter, Finset.mem_map] at hx
    obtain ⟨⟨a, ha, rfl⟩, hmin⟩ := hx
    rw [Finset.mem_map]
    refine ⟨a, ?_, rfl⟩
    rw [argminSet, Finset.mem_filter]
    refine ⟨ha, fun b hb => ?_⟩
    have := hmin (σ.toEmbedding b) (Finset.mem_map_of_mem _ hb)
    simpa [hz] using this
  · intro hx
    rw [Finset.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [argminSet, Finset.mem_filter] at ha ⊢
    refine ⟨Finset.mem_map_of_mem _ ha.1, fun u' hu' => ?_⟩
    rw [Finset.mem_map] at hu'
    obtain ⟨b, hb, rfl⟩ := hu'
    simpa [hz] using ha.2 b hb

lemma jr_out (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N d : ℕ)
    (w : Fin (M N)) (z : Fin N → ℕ) (v : Fin N) (hv : v ∉ nbrW M G N w) :
    jsqdRoute M G N d w z v = 0 := by
  unfold jsqdRoute
  rw [Finset.sum_eq_zero, mul_zero]
  intro U hU
  rw [Finset.mem_powersetCard] at hU
  rw [if_neg]
  intro h
  exact hv (hU.1 (Finset.filter_subset _ _ h))

lemma jr_perm (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N d : ℕ)
    (w : Fin (M N)) (z : Fin N → ℕ) (σ : Equiv.Perm (Fin N)) (hz : ∀ u, z (σ u) = z u)
    (hN : ∀ u, σ u ∈ nbrW M G N w ↔ u ∈ nbrW M G N w) (v : Fin N) :
    jsqdRoute M G N d w z (σ v) = jsqdRoute M G N d w z v := by
  unfold jsqdRoute
  congr 1
  have hz' : ∀ u, z (σ.symm u) = z u := fun u => by simpa using (hz (σ.symm u)).symm
  have hmap : ∀ (τ : Equiv.Perm (Fin N)), (∀ u, τ u ∈ nbrW M G N w ↔ u ∈ nbrW M G N w) →
      ∀ U ∈ (nbrW M G N w).powersetCard (min d (nbrW M G N w).card),
        U.map τ.toEmbedding ∈ (nbrW M G N w).powersetCard (min d (nbrW M G N w).card) := by
    intro τ hτ U hU
    rw [Finset.mem_powersetCard] at hU ⊢
    refine ⟨fun x hx => ?_, by rw [Finset.card_map]; exact hU.2⟩
    rw [Finset.mem_map] at hx
    obtain ⟨b, hb, rfl⟩ := hx
    exact (hτ b).mpr (hU.1 hb)
  have hNs : ∀ u, σ.symm u ∈ nbrW M G N w ↔ u ∈ nbrW M G N w := fun u => by
    simpa using (hN (σ.symm u)).symm
  apply Finset.sum_nbij' (fun U => U.map σ.symm.toEmbedding) (fun U => U.map σ.toEmbedding)
  · exact hmap σ.symm hNs
  · exact hmap σ hN
  · intro U _; ext x; simp [Finset.mem_map_equiv]
  · intro U _; ext x; simp [Finset.mem_map_equiv]
  · intro U _
    rw [argmin_map σ.symm z hz' U, Finset.card_map]
    by_cases h : σ v ∈ argminSet U z
    · rw [if_pos h, if_pos (Finset.mem_map_equiv.mpr (by simpa using h))]
    · rw [if_neg h, if_neg (fun h' => h (by simpa using Finset.mem_map_equiv.mp h'))]

lemma jr_const (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N d : ℕ)
    (w : Fin (M N)) (z : Fin N → ℕ) (v v' : Fin N) (hv : v ∈ nbrW M G N w)
    (hv' : v' ∈ nbrW M G N w) (hzz : z v = z v') :
    jsqdRoute M G N d w z v' = jsqdRoute M G N d w z v := by
  have hz : ∀ u, z (Equiv.swap v v' u) = z u := by
    intro u
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2
    · rw [h1, hzz]
    · rw [h2, hzz]
    · rfl
  have hN : ∀ u, Equiv.swap v v' u ∈ nbrW M G N w ↔ u ∈ nbrW M G N w := by
    intro u
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2
    · rw [h1]; exact ⟨fun _ => hv, fun _ => hv'⟩
    · rw [h2]; exact ⟨fun _ => hv', fun _ => hv⟩
    · exact Iff.rfl
  have := jr_perm M G N d w z (Equiv.swap v v') hz hN v
  rwa [Equiv.swap_apply_left] at this

noncomputable def Hq (n k d a : ℕ) : ℝ := Fq n k a - Gq n d a

lemma jr_level (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N d : ℕ)
    (w : Fin (M N)) (z : Fin N → ℕ) (hd : 1 ≤ d) (hn : 1 ≤ (nbrW M G N w).card) (i : ℕ) :
    ∑ v ∈ (nbrW M G N w).filter (fun u => z u = i), jsqdRoute M G N d w z v
      = Fq (nbrW M G N w).card (min d (nbrW M G N w).card) (Acnt M G N z w i)
        - Fq (nbrW M G N w).card (min d (nbrW M G N w).card) (Acnt M G N z w (i+1)) := by
  unfold jsqdRoute
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hk1 : 1 ≤ min d (nbrW M G N w).card := le_min hd hn
  have hU : ∀ U ∈ (nbrW M G N w).powersetCard (min d (nbrW M G N w).card),
      ∑ v ∈ (nbrW M G N w).filter (fun u => z u = i),
          (if v ∈ argminSet U z then ((argminSet U z).card : ℝ)⁻¹ else 0)
        = if (∀ u ∈ U, i ≤ z u) ∧ ¬ (∀ u ∈ U, i + 1 ≤ z u) then 1 else 0 := by
    intro U hUP
    rw [Finset.mem_powersetCard] at hUP
    have hne : U.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨u0, hu0, hmin⟩ := Finset.exists_min_image U z hne
    have hu0A : u0 ∈ argminSet U z := Finset.mem_filter.mpr ⟨hu0, hmin⟩
    have hAz : ∀ x ∈ argminSet U z, z x = z u0 := fun x hx =>
      le_antisymm ((Finset.mem_filter.mp hx).2 u0 hu0) (hmin x (Finset.mem_filter.mp hx).1)
    by_cases hc : z u0 = i
    · rw [if_pos ⟨fun u hu => hc ▸ hmin u hu, fun h => by have := h u0 hu0; omega⟩]
      rw [← Finset.sum_filter]
      have hsub : ((nbrW M G N w).filter (fun u => z u = i)).filter (fun v => v ∈ argminSet U z)
          = argminSet U z := by
        ext x
        constructor
        · intro hx; exact (Finset.mem_filter.mp hx).2
        · intro hx
          refine Finset.mem_filter.mpr ⟨?_, hx⟩
          exact Finset.mem_filter.mpr ⟨hUP.1 (Finset.filter_subset _ _ hx), (hAz x hx).trans hc⟩
      rw [hsub, Finset.sum_const, nsmul_eq_mul]
      have hpos : (0 : ℝ) < ((argminSet U z).card : ℝ) :=
        Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨u0, hu0A⟩)
      exact mul_inv_cancel₀ hpos.ne'
    · rw [if_neg (fun ⟨h1, h2⟩ => h2 (fun u hu => by
        have := h1 u0 hu0; have := hmin u hu; omega))]
      apply Finset.sum_eq_zero
      intro v hv
      rw [if_neg]
      intro hvA
      exact hc ((hAz v hvA).symm.trans (Finset.mem_filter.mp hv).2)
  rw [Finset.sum_congr rfl hU, Finset.sum_boole]
  have hcard : ∀ j, (((nbrW M G N w).powersetCard (min d (nbrW M G N w).card)).filter
      (fun U => ∀ u ∈ U, j ≤ z u)).card = (Acnt M G N z w j).choose (min d (nbrW M G N w).card) := by
    intro j
    rw [Acnt, ← Finset.card_powersetCard]
    congr 1
    ext U
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨fun x hx => ⟨h1 hx, h3 x hx⟩, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨fun x hx => (h1 hx).1, h2⟩, fun x hx => (h1 hx).2⟩
  have hsplit : ((nbrW M G N w).powersetCard (min d (nbrW M G N w).card)).filter
        (fun U => ∀ u ∈ U, i ≤ z u)
      = ((nbrW M G N w).powersetCard (min d (nbrW M G N w).card)).filter
          (fun U => (∀ u ∈ U, i ≤ z u) ∧ ¬ (∀ u ∈ U, i + 1 ≤ z u))
        ∪ ((nbrW M G N w).powersetCard (min d (nbrW M G N w).card)).filter
          (fun U => ∀ u ∈ U, i + 1 ≤ z u) := by
    ext U
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hP, h⟩
      by_cases h' : ∀ u ∈ U, i + 1 ≤ z u
      · exact Or.inr ⟨hP, h'⟩
      · exact Or.inl ⟨hP, h, h'⟩
    · rintro (⟨hP, h, _⟩ | ⟨hP, h'⟩)
      · exact ⟨hP, h⟩
      · exact ⟨hP, fun u hu => by have := h' u hu; omega⟩
  have hdisj : Disjoint (((nbrW M G N w).powersetCard (min d (nbrW M G N w).card)).filter
          (fun U => (∀ u ∈ U, i ≤ z u) ∧ ¬ (∀ u ∈ U, i + 1 ≤ z u)))
        (((nbrW M G N w).powersetCard (min d (nbrW M G N w).card)).filter
          (fun U => ∀ u ∈ U, i + 1 ≤ z u)) :=
    Finset.disjoint_filter.mpr (fun U _ h1 h2 => h1.2 h2)
  have hc := congrArg Finset.card hsplit
  first
    | rw [Finset.card_union_of_disjoint hdisj] at hc
    | rw [Finset.card_union_eq_card_add_card.mpr hdisj] at hc
  rw [hcard, hcard] at hc
  have hR := congrArg (Nat.cast (R := ℝ)) hc
  push_cast at hR
  unfold Fq
  rw [← sub_div, div_eq_inv_mul]
  congr 1
  linarith

lemma pr_level (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N d : ℕ)
    (w : Fin (M N)) (z : Fin N → ℕ) (v : Fin N) (hv : v ∈ nbrW M G N w) :
    piRoute M G N (jsqdAssign d) w z v
      = (Gq (nbrW M G N w).card d (Acnt M G N z w (z v))
          - Gq (nbrW M G N w).card d (Acnt M G N z w (z v + 1)))
        / (((nbrW M G N w).filter (fun u => z u = z v)).card : ℝ) := by
  unfold piRoute jsqdAssign Gq
  rw [if_pos hv, tail_leqd, tail_leqd]

/-- K3a. -/
theorem tv_jsqd (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N d : ℕ)
    (hd : 1 ≤ d) (w : Fin (M N)) (z : Fin N → ℕ) :
    ∑ v : Fin N, |jsqdRoute M G N d w z v - piRoute M G N (jsqdAssign d) w z v|
      ≤ 2 * (d : ℝ) ^ 3 / (nbrW M G N w).card := by
  have hout : ∀ v ∈ (Finset.univ : Finset (Fin N)), v ∉ nbrW M G N w →
      |jsqdRoute M G N d w z v - piRoute M G N (jsqdAssign d) w z v| = 0 := by
    intro v _ hv
    rw [jr_out M G N d w z v hv]
    unfold piRoute
    rw [if_neg hv]; simp
  rw [← Finset.sum_subset (Finset.subset_univ (nbrW M G N w)) hout]
  rcases Nat.eq_zero_or_pos (nbrW M G N w).card with h0 | hn
  · rw [Finset.card_eq_zero.mp h0]; simp
  have hzB : ∀ v, z v < ∑ u, z u + 1 := fun v => by
    have := Finset.single_le_sum (f := z) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
    omega
  rw [← Finset.sum_fiberwise_of_maps_to (g := z) (t := Finset.range (∑ u, z u + 1))
    (fun v _ => Finset.mem_range.mpr (hzB v))]
  have hlev : ∀ i ∈ Finset.range (∑ u, z u + 1),
      ∑ v ∈ (nbrW M G N w).filter (fun v => z v = i),
          |jsqdRoute M G N d w z v - piRoute M G N (jsqdAssign d) w z v|
        ≤ |Hq (nbrW M G N w).card (min d (nbrW M G N w).card) d (Acnt M G N z w i)
            - Hq (nbrW M G N w).card (min d (nbrW M G N w).card) d (Acnt M G N z w (i+1))| := by
    intro i _
    rcases ((nbrW M G N w).filter (fun v => z v = i)).eq_empty_or_nonempty with hE | ⟨v0, hv0⟩
    · rw [hE, Finset.sum_empty]; exact abs_nonneg _
    have hv0' := Finset.mem_filter.mp hv0
    have hconst : ∀ v ∈ (nbrW M G N w).filter (fun v => z v = i),
        jsqdRoute M G N d w z v - piRoute M G N (jsqdAssign d) w z v
          = jsqdRoute M G N d w z v0 - piRoute M G N (jsqdAssign d) w z v0 := by
      intro v hv
      have hv' := Finset.mem_filter.mp hv
      rw [jr_const M G N d w z v0 v hv0'.1 hv'.1 (hv0'.2.trans hv'.2.symm),
        pr_level M G N d w z v hv'.1, pr_level M G N d w z v0 hv0'.1, hv'.2, hv0'.2]
    have hsumabs : ∑ v ∈ (nbrW M G N w).filter (fun v => z v = i),
          |jsqdRoute M G N d w z v - piRoute M G N (jsqdAssign d) w z v|
        = |∑ v ∈ (nbrW M G N w).filter (fun v => z v = i),
          (jsqdRoute M G N d w z v - piRoute M G N (jsqdAssign d) w z v)| := by
      rw [Finset.sum_congr rfl (fun v hv => congrArg abs (hconst v hv)),
        Finset.sum_congr rfl hconst, Finset.sum_const, Finset.sum_const, nsmul_eq_mul,
        nsmul_eq_mul, abs_mul, Nat.abs_cast]
    have hpr : ∑ v ∈ (nbrW M G N w).filter (fun v => z v = i),
          piRoute M G N (jsqdAssign d) w z v
        = Gq (nbrW M G N w).card d (Acnt M G N z w i)
          - Gq (nbrW M G N w).card d (Acnt M G N z w (i + 1)) := by
      rw [Finset.sum_congr rfl (fun v hv => by
        rw [pr_level M G N d w z v (Finset.mem_filter.mp hv).1, (Finset.mem_filter.mp hv).2])]
      rw [Finset.sum_const, nsmul_eq_mul]
      have hpos : (0 : ℝ) < (((nbrW M G N w).filter (fun u => z u = i)).card : ℝ) :=
        Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨v0, hv0⟩)
      field_simp
    rw [hsumabs, Finset.sum_sub_distrib, jr_level M G N d w z hd hn i, hpr]
    apply le_of_eq
    unfold Hq
    congr 1
    ring
  have hA0 := Acnt_le M G N z w 0
  calc ∑ i ∈ Finset.range (∑ u, z u + 1), ∑ v ∈ (nbrW M G N w).filter (fun v => z v = i),
          |jsqdRoute M G N d w z v - piRoute M G N (jsqdAssign d) w z v|
        ≤ ∑ i ∈ Finset.range (∑ u, z u + 1),
          |Hq (nbrW M G N w).card (min d (nbrW M G N w).card) d (Acnt M G N z w i)
            - Hq (nbrW M G N w).card (min d (nbrW M G N w).card) d (Acnt M G N z w (i+1))| :=
          Finset.sum_le_sum hlev
    _ ≤ ∑ a ∈ Finset.Ico (Acnt M G N z w (∑ u, z u + 1)) (Acnt M G N z w 0),
          |Hq (nbrW M G N w).card (min d (nbrW M G N w).card) d (a+1)
            - Hq (nbrW M G N w).card (min d (nbrW M G N w).card) d a| :=
          chain _ (fun i => Acnt M G N z w i) (Acnt_anti M G N z w) _
    _ ≤ ∑ a ∈ Finset.range (nbrW M G N w).card,
          |Hq (nbrW M G N w).card (min d (nbrW M G N w).card) d (a+1)
            - Hq (nbrW M G N w).card (min d (nbrW M G N w).card) d a| := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro a ha
            rw [Finset.mem_Ico] at ha
            rw [Finset.mem_range]
            omega
          · intro _ _ _; exact abs_nonneg _
    _ ≤ 2 * (d : ℝ) ^ 3 / (nbrW M G N w).card := tv_num _ d hn hd

/-! ### Row sums (session 9): both routing laws are probability vectors on a nonempty `𝒩_w`. -/

lemma Acnt_zero (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ)
    (z : Fin N → ℕ) (w : Fin (M N)) : Acnt M G N z w 0 = (nbrW M G N w).card := by
  unfold Acnt
  congr 1
  exact Finset.filter_true_of_mem (fun v _ => Nat.zero_le _)

lemma Acnt_big (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ)
    (z : Fin N → ℕ) (w : Fin (M N)) : Acnt M G N z w (∑ u, z u + 1) = 0 := by
  unfold Acnt
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro v _ h
  have := Finset.single_le_sum (f := z) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
  omega

lemma Acnt_split (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ)
    (z : Fin N → ℕ) (w : Fin (M N)) (i : ℕ) :
    Acnt M G N z w i = Acnt M G N z w (i+1) + ((nbrW M G N w).filter (fun u => z u = i)).card := by
  unfold Acnt
  have hdisj : Disjoint ((nbrW M G N w).filter (fun v => i + 1 ≤ z v))
      ((nbrW M G N w).filter (fun u => z u = i)) :=
    Finset.disjoint_filter.mpr (fun v _ h1 h2 => by omega)
  have hU : (nbrW M G N w).filter (fun v => i ≤ z v)
      = (nbrW M G N w).filter (fun v => i + 1 ≤ z v) ∪ (nbrW M G N w).filter (fun u => z u = i) := by
    ext v
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hv, h⟩
      by_cases h' : z v = i
      · exact Or.inr ⟨hv, h'⟩
      · exact Or.inl ⟨hv, by omega⟩
    · rintro (⟨hv, h⟩ | ⟨hv, h⟩)
      · exact ⟨hv, by omega⟩
      · exact ⟨hv, by omega⟩
  rw [hU]
  first
    | exact Finset.card_union_of_disjoint hdisj
    | exact Finset.card_union_eq_card_add_card.mpr hdisj

lemma level_sum (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ)
    (w : Fin (M N)) (z : Fin N → ℕ) (f : Fin N → ℝ) (H : ℕ → ℝ)
    (hout : ∀ v, v ∉ nbrW M G N w → f v = 0)
    (hlev : ∀ i, ∑ v ∈ (nbrW M G N w).filter (fun u => z u = i), f v
      = H (Acnt M G N z w i) - H (Acnt M G N z w (i+1))) :
    ∑ v, f v = H (nbrW M G N w).card - H 0 := by
  rw [← Finset.sum_subset (Finset.subset_univ (nbrW M G N w)) (fun v _ hv => hout v hv)]
  have hzB : ∀ v, z v < ∑ u, z u + 1 := fun v => by
    have := Finset.single_le_sum (f := z) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
    omega
  rw [← Finset.sum_fiberwise_of_maps_to (g := z) (t := Finset.range (∑ u, z u + 1))
    (fun v _ => Finset.mem_range.mpr (hzB v))]
  rw [Finset.sum_congr rfl (fun i _ => hlev i)]
  have := Finset.sum_range_sub' (fun i => H (Acnt M G N z w i)) (∑ u, z u + 1)
  simp only [Acnt_zero, Acnt_big] at this
  exact this

theorem sum_jr (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N d : ℕ)
    (hd : 1 ≤ d) (w : Fin (M N)) (z : Fin N → ℕ) (hn : 1 ≤ (nbrW M G N w).card) :
    ∑ v, jsqdRoute M G N d w z v = 1 := by
  rw [level_sum M G N w z _ (Fq (nbrW M G N w).card (min d (nbrW M G N w).card))
    (jr_out M G N d w z) (jr_level M G N d w z hd hn)]
  have hk : min d (nbrW M G N w).card ≤ (nbrW M G N w).card := min_le_right _ _
  have hk1 : 1 ≤ min d (nbrW M G N w).card := le_min hd hn
  unfold Fq
  have hC : ((nbrW M G N w).card.choose (min d (nbrW M G N w).card) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos hk).ne'
  rw [div_self hC, Nat.choose_eq_zero_of_lt (by omega : 0 < min d (nbrW M G N w).card)]
  simp

theorem sum_pr (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N d : ℕ)
    (hd : 1 ≤ d) (w : Fin (M N)) (z : Fin N → ℕ) (hn : 1 ≤ (nbrW M G N w).card) :
    ∑ v, piRoute M G N (jsqdAssign d) w z v = 1 := by
  have hout : ∀ v, v ∉ nbrW M G N w → piRoute M G N (jsqdAssign d) w z v = 0 := by
    intro v hv; unfold piRoute; rw [if_neg hv]
  have hlev : ∀ i, ∑ v ∈ (nbrW M G N w).filter (fun u => z u = i),
      piRoute M G N (jsqdAssign d) w z v
        = Gq (nbrW M G N w).card d (Acnt M G N z w i)
          - Gq (nbrW M G N w).card d (Acnt M G N z w (i + 1)) := by
    intro i
    rcases ((nbrW M G N w).filter (fun v => z v = i)).eq_empty_or_nonempty with hE | ⟨v0, hv0⟩
    · rw [hE, Finset.sum_empty, Acnt_split M G N z w i, hE, Finset.card_empty, add_zero, sub_self]
    rw [Finset.sum_congr rfl (fun v hv => by
      rw [pr_level M G N d w z v (Finset.mem_filter.mp hv).1, (Finset.mem_filter.mp hv).2])]
    rw [Finset.sum_const, nsmul_eq_mul]
    have hpos : (0 : ℝ) < (((nbrW M G N w).filter (fun u => z u = i)).card : ℝ) :=
      Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨v0, hv0⟩)
    field_simp
  rw [level_sum M G N w z _ (Gq (nbrW M G N w).card d) hout hlev]
  unfold Gq
  have hn' : ((nbrW M G N w).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [div_self hn', Nat.cast_zero, zero_div, zero_pow (by omega : d ≠ 0)]
  simp

end SC77K3A

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace SC77K3D2

open StrictCompatLB.MeanField

/-! K3d-2a: a coupling of two sub-probability vectors with equal mass whose off-diagonal mass is
at most `∑ |a - b|`, the coupled lbKernel on pairs of states, its two marginals, and the
conditional kernel `Q` used to build the `piRoute` chain from the given JSQ(d) chain. -/

section Cpl

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Excess mass of `a` over `min a b`. -/
noncomputable def rr (a b : V → ℝ) : ℝ := ∑ v, (a v - min (a v) (b v))

/-- The coupling: diagonal `min`, plus the product of the excesses normalised by `rr`. -/
noncomputable def cpl (a b : V → ℝ) (v v' : V) : ℝ :=
  (if v = v' then min (a v) (b v) else 0) +
    (if rr a b = 0 then 0 else (a v - min (a v) (b v)) * (b v' - min (a v') (b v')) / rr a b)

lemma rr_nonneg (a b : V → ℝ) : 0 ≤ rr a b :=
  Finset.sum_nonneg (fun v _ => sub_nonneg.mpr (min_le_left _ _))

lemma rr_b (a b : V → ℝ) (hs : ∑ v, a v = ∑ v, b v) :
    ∑ v, (b v - min (a v) (b v)) = rr a b := by
  unfold rr
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hs]

lemma cpl_extra_nonneg (a b : V → ℝ) (v v' : V) :
    0 ≤ (if rr a b = 0 then 0 else (a v - min (a v) (b v)) * (b v' - min (a v') (b v')) / rr a b) := by
  split_ifs
  · exact le_refl _
  · exact div_nonneg (mul_nonneg (sub_nonneg.mpr (min_le_left _ _))
      (sub_nonneg.mpr (min_le_right _ _))) (rr_nonneg a b)

lemma cpl_nonneg (a b : V → ℝ) (ha : ∀ v, 0 ≤ a v) (hb : ∀ v, 0 ≤ b v) (v v' : V) :
    0 ≤ cpl a b v v' := by
  unfold cpl
  have h1 : 0 ≤ (if v = v' then min (a v) (b v) else 0) := by
    split_ifs
    · exact le_min (ha v) (hb v)
    · exact le_refl _
  exact add_nonneg h1 (cpl_extra_nonneg a b v v')

lemma cpl_row (a b : V → ℝ) (hs : ∑ v, a v = ∑ v, b v) (v : V) :
    ∑ v', cpl a b v v' = a v := by
  unfold cpl
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq Finset.univ v (fun _ => min (a v) (b v)),
    if_pos (Finset.mem_univ v)]
  by_cases hr : rr a b = 0
  · simp only [hr, if_true, Finset.sum_const_zero, add_zero]
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun u _ => sub_nonneg.mpr (min_le_left (a u) (b u)))).mp hr v (Finset.mem_univ v)
    linarith
  · simp only [hr, if_false]
    rw [← Finset.sum_div, ← Finset.mul_sum, rr_b a b hs, mul_div_assoc, div_self hr]
    ring

lemma cpl_col (a b : V → ℝ) (hs : ∑ v, a v = ∑ v, b v) (v' : V) :
    ∑ v, cpl a b v v' = b v' := by
  unfold cpl
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ v' (fun u => min (a u) (b u)),
    if_pos (Finset.mem_univ v')]
  by_cases hr : rr a b = 0
  · simp only [hr, if_true, Finset.sum_const_zero, add_zero]
    have hr' := rr_b a b hs
    rw [hr] at hr'
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun u _ => sub_nonneg.mpr (min_le_right (a u) (b u)))).mp hr' v' (Finset.mem_univ v')
    linarith
  · simp only [hr, if_false]
    rw [← Finset.sum_div, ← Finset.sum_mul]
    have hc : (∑ i, (a i - min (a i) (b i))) * (b v' - min (a v') (b v')) / rr a b
        = b v' - min (a v') (b v') := by
      change rr a b * (b v' - min (a v') (b v')) / rr a b = _
      field_simp
    linarith

/-- Off-diagonal mass is at most `rr ≤ ∑ |a - b|`. -/
lemma cpl_off (a b : V → ℝ) (hs : ∑ v, a v = ∑ v, b v) :
    ∑ v, ∑ v', (if v = v' then 0 else cpl a b v v') ≤ ∑ v, |a v - b v| := by
  have hle : ∀ v v', (if v = v' then 0 else cpl a b v v')
      ≤ (if rr a b = 0 then 0 else (a v - min (a v) (b v)) * (b v' - min (a v') (b v')) / rr a b) := by
    intro v v'
    by_cases h : v = v'
    · rw [if_pos h]; exact cpl_extra_nonneg a b v v'
    · rw [if_neg h]; unfold cpl; rw [if_neg h, zero_add]
  have htot : ∑ v, ∑ v', (if rr a b = 0 then 0 else
      (a v - min (a v) (b v)) * (b v' - min (a v') (b v')) / rr a b) ≤ rr a b := by
    by_cases hr : rr a b = 0
    · simp only [hr, if_true, Finset.sum_const_zero, le_refl]
    · simp only [hr, if_false]
      rw [Finset.sum_congr rfl (fun v _ => by rw [← Finset.sum_div, ← Finset.mul_sum])]
      rw [← Finset.sum_div, ← Finset.sum_mul, rr_b a b hs]
      change rr a b * rr a b / rr a b ≤ rr a b
      rw [mul_div_assoc, div_self hr, mul_one]
  have hrr : rr a b ≤ ∑ v, |a v - b v| := by
    unfold rr
    apply Finset.sum_le_sum
    intro v _
    rcases le_total (a v) (b v) with h | h
    · rw [min_eq_left h, sub_self]; exact abs_nonneg _
    · rw [min_eq_right h, abs_of_nonneg (by linarith)]
  calc _ ≤ _ := Finset.sum_le_sum (fun v _ => Finset.sum_le_sum (fun v' _ => hle v v'))
    _ ≤ rr a b := htot
    _ ≤ _ := hrr

end Cpl

section Kernel

variable (lam : ℝ) (M : ℕ → ℕ) (N : ℕ) (ra rb : Fin (M N) → (Fin N → ℕ) → Fin N → ℝ)

/-- The coupled kernel on pairs `(x, z)`: shared event type, dispatcher and departing server;
arrival servers drawn from `cpl (ra w x) (rb w z)`. -/
noncomputable def Kc (p p' : (Fin N → ℕ) × (Fin N → ℕ)) : ℝ :=
  lam / (lam + 1) * (1 / (M N : ℝ)) *
      ∑ w : Fin (M N), ∑ v : Fin N, ∑ v' : Fin N,
        cpl (ra w p.1) (rb w p.2) v v' * (if p'.1 = arrive p.1 v then 1 else 0)
          * (if p'.2 = arrive p.2 v' then 1 else 0) +
    1 / (lam + 1) * (1 / (N : ℝ)) * ∑ v : Fin N,
      (if p'.1 = depart p.1 v then 1 else 0) * (if p'.2 = depart p.2 v then 1 else 0)

lemma Kc_nonneg (hlam : 0 ≤ lam) (hra : ∀ w x v, 0 ≤ ra w x v) (hrb : ∀ w x v, 0 ≤ rb w x v)
    (p p' : (Fin N → ℕ) × (Fin N → ℕ)) : 0 ≤ Kc lam M N ra rb p p' := by
  unfold Kc
  have hI : ∀ (P : Prop) [Decidable P], (0 : ℝ) ≤ if P then 1 else 0 := by
    intro P _; split_ifs <;> norm_num
  apply add_nonneg
  · apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun w _ => Finset.sum_nonneg (fun v _ => Finset.sum_nonneg
      (fun v' _ => mul_nonneg (mul_nonneg (cpl_nonneg _ _ (hra w p.1) (hrb w p.2) v v') (hI _)) (hI _))))
  · apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun v _ => mul_nonneg (hI _) (hI _))

/-- First marginal: summing out the second coordinate gives the kernel of `ra`. -/
lemma Kc_marg1 (hs : ∀ w x z, ∑ v, ra w x v = ∑ v, rb w z v) (x z x' : Fin N → ℕ) :
    HasSum (fun z' => Kc lam M N ra rb (x, z) (x', z')) (lbKernel lam M N ra x x') := by
  have hterm : ∀ w v v', HasSum (fun z' : Fin N → ℕ =>
      cpl (ra w x) (rb w z) v v' * (if x' = arrive x v then 1 else 0)
        * (if z' = arrive z v' then 1 else 0))
      (cpl (ra w x) (rb w z) v v' * (if x' = arrive x v then 1 else 0)) := by
    intro w v v'
    have h := (hasSum_ite_eq (arrive z v') (1 : ℝ)).mul_left
      (cpl (ra w x) (rb w z) v v' * (if x' = arrive x v then 1 else 0))
    rw [mul_one] at h
    exact h
  have hdep : ∀ v, HasSum (fun z' : Fin N → ℕ =>
      (if x' = depart x v then (1 : ℝ) else 0) * (if z' = depart z v then 1 else 0))
      (if x' = depart x v then (1 : ℝ) else 0) := by
    intro v
    have h := (hasSum_ite_eq (depart z v) (1 : ℝ)).mul_left (if x' = depart x v then (1 : ℝ) else 0)
    simpa using h
  have hA := (hasSum_sum (s := Finset.univ) (fun w _ => hasSum_sum (s := Finset.univ) (fun v _ =>
    hasSum_sum (s := Finset.univ) (fun v' _ => hterm w v v')))).mul_left (lam / (lam + 1) * (1 / (M N : ℝ)))
  have hD := (hasSum_sum (s := Finset.univ) (fun v _ => hdep v)).mul_left (1 / (lam + 1) * (1 / (N : ℝ)))
  have h := hA.add hD
  have hv : lbKernel lam M N ra x x' = lam / (lam + 1) * (1 / (M N : ℝ)) *
      ∑ w : Fin (M N), ∑ v : Fin N, ∑ v' : Fin N,
        cpl (ra w x) (rb w z) v v' * (if x' = arrive x v then 1 else 0) +
      1 / (lam + 1) * (1 / (N : ℝ)) * ∑ v : Fin N, (if x' = depart x v then (1 : ℝ) else 0) := by
    unfold lbKernel
    congr 2
    apply Finset.sum_congr rfl
    intro w _
    apply Finset.sum_congr rfl
    intro v _
    rw [← Finset.sum_mul, cpl_row _ _ (hs w x z) v]
  rw [hv]
  exact h

/-- Second marginal: summing out the first coordinate gives the kernel of `rb`. -/
lemma Kc_marg2 (hs : ∀ w x z, ∑ v, ra w x v = ∑ v, rb w z v) (x z z' : Fin N → ℕ) :
    HasSum (fun x' => Kc lam M N ra rb (x, z) (x', z')) (lbKernel lam M N rb z z') := by
  have hterm : ∀ w v v', HasSum (fun x' : Fin N → ℕ =>
      cpl (ra w x) (rb w z) v v' * (if x' = arrive x v then 1 else 0)
        * (if z' = arrive z v' then 1 else 0))
      (cpl (ra w x) (rb w z) v v' * (if z' = arrive z v' then 1 else 0)) := by
    intro w v v'
    have h := (hasSum_ite_eq (arrive x v) (1 : ℝ)).mul_left
      (cpl (ra w x) (rb w z) v v' * (if z' = arrive z v' then 1 else 0))
    rw [mul_one] at h
    have hf : (fun x' : Fin N → ℕ => cpl (ra w x) (rb w z) v v' * (if x' = arrive x v then 1 else 0)
          * (if z' = arrive z v' then 1 else 0))
        = (fun x' : Fin N → ℕ => cpl (ra w x) (rb w z) v v' * (if z' = arrive z v' then 1 else 0)
          * (if x' = arrive x v then 1 else 0)) := by
      funext x'; ring
    rw [hf]; exact h
  have hdep : ∀ v, HasSum (fun x' : Fin N → ℕ =>
      (if x' = depart x v then (1 : ℝ) else 0) * (if z' = depart z v then 1 else 0))
      (if z' = depart z v then (1 : ℝ) else 0) := by
    intro v
    have h := (hasSum_ite_eq (depart x v) (1 : ℝ)).mul_left (if z' = depart z v then (1 : ℝ) else 0)
    rw [mul_one] at h
    have hf : (fun x' : Fin N → ℕ => (if x' = depart x v then (1 : ℝ) else 0)
          * (if z' = depart z v then 1 else 0))
        = (fun x' : Fin N → ℕ => (if z' = depart z v then (1 : ℝ) else 0)
          * (if x' = depart x v then 1 else 0)) := by
      funext x'; ring
    rw [hf]; exact h
  have hA := (hasSum_sum (s := Finset.univ) (fun w _ => hasSum_sum (s := Finset.univ) (fun v _ =>
    hasSum_sum (s := Finset.univ) (fun v' _ => hterm w v v')))).mul_left (lam / (lam + 1) * (1 / (M N : ℝ)))
  have hD := (hasSum_sum (s := Finset.univ) (fun v _ => hdep v)).mul_left (1 / (lam + 1) * (1 / (N : ℝ)))
  have h := hA.add hD
  have hv : lbKernel lam M N rb z z' = lam / (lam + 1) * (1 / (M N : ℝ)) *
      ∑ w : Fin (M N), ∑ v : Fin N, ∑ v' : Fin N,
        cpl (ra w x) (rb w z) v v' * (if z' = arrive z v' then 1 else 0) +
      1 / (lam + 1) * (1 / (N : ℝ)) * ∑ v : Fin N, (if z' = depart z v then (1 : ℝ) else 0) := by
    unfold lbKernel
    congr 2
    apply Finset.sum_congr rfl
    intro w _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v' _
    rw [← Finset.sum_mul, cpl_col _ _ (hs w x z) v']
  rw [hv]
  exact h

/-- Conditional kernel of the `rb`-chain's next state given `(x, z, x')`. -/
noncomputable def Q (x z x' z' : Fin N → ℕ) : ℝ :=
  if lbKernel lam M N ra x x' = 0 then (if z' = z then 1 else 0)
  else Kc lam M N ra rb (x, z) (x', z') / lbKernel lam M N ra x x'

lemma Q_nonneg (hlam : 0 ≤ lam) (hra : ∀ w x v, 0 ≤ ra w x v) (hrb : ∀ w x v, 0 ≤ rb w x v)
    (x z x' z' : Fin N → ℕ) : 0 ≤ Q lam M N ra rb x z x' z' := by
  unfold Q
  split_ifs with h h'
  · norm_num
  · norm_num
  · have hk0 : 0 ≤ lbKernel lam M N ra x x' := by
      unfold lbKernel
      have hI : ∀ (P : Prop) [Decidable P], (0 : ℝ) ≤ if P then 1 else 0 := by
        intro P _; split_ifs <;> norm_num
      apply add_nonneg
      · apply mul_nonneg (by positivity)
        exact Finset.sum_nonneg (fun w _ => Finset.sum_nonneg (fun v _ =>
          mul_nonneg (hra w x v) (hI _)))
      · apply mul_nonneg (by positivity)
        exact Finset.sum_nonneg (fun v _ => hI _)
    exact div_nonneg (Kc_nonneg lam M N ra rb hlam hra hrb _ _) hk0

lemma Q_hasSum (hs : ∀ w x z, ∑ v, ra w x v = ∑ v, rb w z v) (x z x' : Fin N → ℕ) :
    HasSum (Q lam M N ra rb x z x') 1 := by
  unfold Q
  by_cases h : lbKernel lam M N ra x x' = 0
  · simp only [h, if_true]
    exact hasSum_ite_eq z 1
  · simp only [h, if_false]
    have := (Kc_marg1 lam M N ra rb hs x z x').div_const (lbKernel lam M N ra x x')
    rwa [div_self h] at this

/-- `K(x, x') Q(x, z, x', z') = Kc((x, z), (x', z'))`. -/
lemma K_mul_Q (hlam : 0 ≤ lam) (hra : ∀ w x v, 0 ≤ ra w x v) (hrb : ∀ w x v, 0 ≤ rb w x v)
    (hs : ∀ w x z, ∑ v, ra w x v = ∑ v, rb w z v) (x z x' z' : Fin N → ℕ) :
    lbKernel lam M N ra x x' * Q lam M N ra rb x z x' z' = Kc lam M N ra rb (x, z) (x', z') := by
  unfold Q
  by_cases h : lbKernel lam M N ra x x' = 0
  · simp only [h, if_true, zero_mul]
    have hm := Kc_marg1 lam M N ra rb hs x z x'
    rw [h] at hm
    have := (hasSum_zero_iff_of_nonneg (fun z'' => Kc_nonneg lam M N ra rb hlam hra hrb
      (x, z) (x', z''))).mp hm
    exact (congrFun this z').symm
  · simp only [h, if_false]
    field_simp

/-- The marginal identity in the `ℝ≥0∞` form used with `markov_int`. -/
lemma marg_ennreal (hlam : 0 ≤ lam) (hra : ∀ w x v, 0 ≤ ra w x v) (hrb : ∀ w x v, 0 ≤ rb w x v)
    (hs : ∀ w x z, ∑ v, ra w x v = ∑ v, rb w z v) (x z z' : Fin N → ℕ) :
    ∑' x', ENNReal.ofReal (lbKernel lam M N ra x x') * ENNReal.ofReal (Q lam M N ra rb x z x' z')
      = ENNReal.ofReal (lbKernel lam M N rb z z') := by
  have hk0 : ∀ x', 0 ≤ lbKernel lam M N ra x x' := by
    intro x'
    unfold lbKernel
    have hI : ∀ (P : Prop) [Decidable P], (0 : ℝ) ≤ if P then 1 else 0 := by
      intro P _; split_ifs <;> norm_num
    apply add_nonneg
    · apply mul_nonneg (by positivity)
      exact Finset.sum_nonneg (fun w _ => Finset.sum_nonneg (fun v _ =>
        mul_nonneg (hra w x v) (hI _)))
    · apply mul_nonneg (by positivity)
      exact Finset.sum_nonneg (fun v _ => hI _)
  have heq : ∀ x', ENNReal.ofReal (lbKernel lam M N ra x x') * ENNReal.ofReal (Q lam M N ra rb x z x' z')
      = ENNReal.ofReal (Kc lam M N ra rb (x, z) (x', z')) := by
    intro x'
    rw [← ENNReal.ofReal_mul (hk0 x'), K_mul_Q lam M N ra rb hlam hra hrb hs]
  rw [tsum_congr heq, ← ENNReal.ofReal_tsum_of_nonneg
    (fun x' => Kc_nonneg lam M N ra rb hlam hra hrb _ _) (Kc_marg2 lam M N ra rb hs x z z').summable,
    (Kc_marg2 lam M N ra rb hs x z z').tsum_eq]

end Kernel

end SC77K3D2

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace SC77K3D

/-! K3d part 1: Markov property in integral form, derived from the cylinder formula of
`IsUniformizedProcess`. Used (a) to show that the coupled chain `Z` built on `Ω × E` from the
given chain `Y` and independent random maps is a `piRoute` chain, and (b) for the drift of the
mismatch count `D`. -/

section Markov

variable {S : Type} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S] [DecidableEq S]

/-- The path prefix `(Y 0, …, Y n)`. -/
def pre {Ω : Type*} (Y : ℕ → Ω → S) (n : ℕ) (ω : Ω) : Fin (n + 1) → S := fun i => Y i ω

lemma measurable_pre {Ω : Type*} [MeasurableSpace Ω] (Y : ℕ → Ω → S)
    (hY : ∀ n, Measurable (Y n)) (n : ℕ) : Measurable (pre Y n) :=
  measurable_pi_lambda _ (fun i => hY i)

/-- The extension of a prefix `xs` by a last state `x'`. -/
def ext {n : ℕ} (xs : Fin (n + 1) → S) (x' : S) : ℕ → S :=
  fun j => if h : j ≤ n then xs ⟨j, by omega⟩ else x'

lemma pre_preimage {Ω : Type*} (Y : ℕ → Ω → S) (n : ℕ) (xs : Fin (n + 1) → S) (x' : S) :
    pre Y n ⁻¹' {xs} = {ω | ∀ j ≤ n, Y j ω = ext xs x' j} := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
  constructor
  · intro h j hj
    rw [ext, dif_pos hj, ← h]
    rfl
  · intro h
    funext i
    have := h i.1 (by omega)
    rw [ext, dif_pos (by omega)] at this
    exact this

lemma pair_preimage {Ω : Type*} (Y : ℕ → Ω → S) (n : ℕ) (xs : Fin (n + 1) → S) (x' : S) :
    (fun ω => (pre Y n ω, Y (n + 1) ω)) ⁻¹' {(xs, x')}
      = {ω | ∀ j ≤ n + 1, Y j ω = ext xs x' j} := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2⟩ j hj
    by_cases hjn : j ≤ n
    · rw [ext, dif_pos hjn, ← h1]; rfl
    · have : j = n + 1 := by omega
      subst this
      rw [ext, dif_neg (by omega)]; exact h2
  · intro h
    refine ⟨?_, ?_⟩
    · funext i
      have := h i.1 (by omega)
      rw [ext, dif_pos (by omega)] at this
      exact this
    · have := h (n + 1) le_rfl
      rw [ext, dif_neg (by omega)] at this
      exact this

/-- Markov property in integral form. -/
theorem markov_int {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (K : S → S → ℝ)
    (hK : ∀ a b, 0 ≤ K a b) (z₀ : S) (Y : ℕ → Ω → S) (hY : ∀ n, Measurable (Y n))
    (hcyl : ∀ (n : ℕ) (zs : ℕ → S), P {ω | ∀ j ≤ n, Y j ω = zs j} =
      ENNReal.ofReal ((if zs 0 = z₀ then 1 else 0) * ∏ j ∈ Finset.range n, K (zs j) (zs (j + 1))))
    (n : ℕ) (H : (Fin (n + 1) → S) → S → ℝ≥0∞) :
    ∫⁻ ω, H (pre Y n ω) (Y (n + 1) ω) ∂P
      = ∫⁻ ω, ∑' x', ENNReal.ofReal (K (Y n ω) x') * H (pre Y n ω) x' ∂P := by
  have hpre := measurable_pre Y hY n
  have hV : Measurable (fun ω => (pre Y n ω, Y (n + 1) ω)) := hpre.prodMk (hY _)
  have hL := lintegral_map (μ := P) (f := fun c : (Fin (n + 1) → S) × S => H c.1 c.2)
    (measurable_of_countable _) hV
  have hR := lintegral_map (μ := P)
    (f := fun xs : Fin (n + 1) → S => ∑' x', ENNReal.ofReal (K (xs (Fin.last n)) x') * H xs x')
    (measurable_of_countable _) hpre
  simp only at hL hR
  rw [← hL]
  have hR' : ∫⁻ ω, ∑' x', ENNReal.ofReal (K (Y n ω) x') * H (pre Y n ω) x' ∂P
      = ∫⁻ xs, ∑' x', ENNReal.ofReal (K (xs (Fin.last n)) x') * H xs x' ∂(P.map (pre Y n)) := by
    rw [hR]; rfl
  rw [hR', lintegral_countable', lintegral_countable']
  refine (ENNReal.tsum_prod (f := fun xs x' =>
    H xs x' * (P.map (fun ω => (pre Y n ω, Y (n + 1) ω))) {(xs, x')})).trans ?_
  apply tsum_congr
  intro xs
  rw [← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro x'
  rw [Measure.map_apply hV (measurableSet_singleton _),
    Measure.map_apply hpre (measurableSet_singleton _),
    pair_preimage Y n xs x', pre_preimage Y n xs x', hcyl, hcyl, Finset.prod_range_succ]
  have hlast : ext xs x' n = xs (Fin.last n) := by rw [ext, dif_pos le_rfl]; rfl
  have hnext : ext xs x' (n + 1) = x' := by rw [ext, dif_neg (by omega)]
  rw [hlast, hnext]
  have hnn : 0 ≤ (if ext xs x' 0 = z₀ then (1 : ℝ) else 0) *
      ∏ j ∈ Finset.range n, K (ext xs x' j) (ext xs x' (j + 1)) := by
    apply mul_nonneg (by split_ifs <;> norm_num)
    exact Finset.prod_nonneg (fun j _ => hK _ _)
  rw [← mul_assoc, ENNReal.ofReal_mul hnn]
  ring

end Markov

end SC77K3D

namespace SC77K3D3

open SC77K3D

/-! K3d-2b: the second chain `Z` built from the given chain `Y` and independent random maps
`g n : S × S × S → S` (rows `Q x z x'`), and its cylinder law on `Ω × E`. -/

variable {S : Type} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S] [DecidableEq S]

noncomputable def vecMeasure (v : S → ℝ) : Measure S :=
  Measure.sum (fun z => ENNReal.ofReal (v z) • Measure.dirac z)

theorem vecMeasure_singleton (v : S → ℝ) (z : S) :
    vecMeasure v {z} = ENNReal.ofReal (v z) := by
  rw [vecMeasure, Measure.sum_apply _ (measurableSet_singleton z)]
  simp only [Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (measurableSet_singleton z)]
  rw [tsum_eq_single z]
  · simp
  · intro b hb
    simp [Set.indicator, hb]

theorem vecMeasure_isProb (v : S → ℝ) (h0 : ∀ z, 0 ≤ v z) (h1 : HasSum v 1) :
    IsProbabilityMeasure (vecMeasure v) := by
  constructor
  rw [vecMeasure, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg h0 h1.summable, h1.tsum_eq, ENNReal.ofReal_one]

/-- The second chain, driven by the first chain `y` and random maps `g`. -/
def Zmap (z₀ : S) (y : ℕ → S) (g : ℕ → S × S × S → S) : ℕ → S
  | 0 => z₀
  | n + 1 => g n (y n, Zmap z₀ y g n, y (n + 1))

theorem measurable_Zmap (z₀ : S) :
    Measurable (fun p : (ℕ → S) × (ℕ → S × S × S → S) => Zmap z₀ p.1 p.2) := by
  refine measurable_pi_iff.2 fun n => ?_
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hev : Measurable (fun q : (S × S × S → S) × (S × S × S) => q.1 q.2) :=
      measurable_from_prod_countable_left fun r => measurable_pi_apply r
    have hrow : Measurable (fun p : (ℕ → S) × (ℕ → S × S × S → S) =>
        (p.1 n, Zmap z₀ p.1 p.2 n, p.1 (n + 1))) :=
      ((measurable_pi_apply n).comp measurable_fst).prodMk
        (ih.prodMk ((measurable_pi_apply (n + 1)).comp measurable_fst))
    exact hev.comp (((measurable_pi_apply n).comp measurable_snd).prodMk hrow)

lemma Zmap_set (z₀ : S) (y : ℕ → S) (n : ℕ) (zs : ℕ → S) (h0 : zs 0 = z₀) :
    {g | ∀ j ≤ n, Zmap z₀ y g j = zs j}
      = {g | ∀ j < n, g j (y j, zs j, y (j + 1)) = zs (j + 1)} := by
  ext g
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h j hj
    have h1 := h j hj.le
    have h2 := h (j + 1) hj
    simp only [Zmap] at h2
    rw [h1] at h2
    exact h2
  · intro hs j hj
    induction j with
    | zero => simp only [Zmap]; exact h0.symm
    | succ j ih =>
      simp only [Zmap]
      rw [ih (by omega)]
      exact hs j (by omega)

lemma Zmap_set_empty (z₀ : S) (y : ℕ → S) (n : ℕ) (zs : ℕ → S) (h0 : zs 0 ≠ z₀) :
    {g | ∀ j ≤ n, Zmap z₀ y g j = zs j} = ∅ := by
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro hg
  have := hg 0 (Nat.zero_le _)
  simp only [Zmap] at this
  exact h0 this.symm

/-- Product of the conditional weights along the paths. -/
noncomputable def gprod {Ω : Type*} (Q : S → S → S → S → ℝ) (Y : ℕ → Ω → S) (zs : ℕ → S)
    (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ∏ j ∈ Finset.range n, ENNReal.ofReal (Q (Y j ω) (zs j) (Y (j + 1) ω) (zs (j + 1)))

noncomputable def Hf (Q : S → S → S → S → ℝ) (zs : ℕ → S) (n : ℕ) (xs : Fin (n + 1) → S)
    (x' : S) : ℝ≥0∞ :=
  ∏ j ∈ Finset.range (n + 1), ENNReal.ofReal (Q (ext xs x' j) (zs j) (ext xs x' (j + 1)) (zs (j + 1)))

lemma ext_pre_le {Ω : Type*} (Y : ℕ → Ω → S) (n : ℕ) (ω : Ω) (x' : S) (j : ℕ) (hj : j ≤ n) :
    ext (pre Y n ω) x' j = Y j ω := by
  rw [ext, dif_pos hj]; rfl

lemma ext_succ' {n : ℕ} (xs : Fin (n + 1) → S) (x' : S) : ext xs x' (n + 1) = x' := by
  rw [ext, dif_neg (by omega)]

lemma measurable_gprod {Ω : Type*} [MeasurableSpace Ω] (Q : S → S → S → S → ℝ)
    (Y : ℕ → Ω → S) (hY : ∀ n, Measurable (Y n)) (zs : ℕ → S) (n : ℕ) :
    Measurable (gprod Q Y zs n) := by
  unfold gprod
  exact Finset.measurable_prod _ (fun j _ =>
    (measurable_of_countable (fun p : S × S => ENNReal.ofReal (Q p.1 (zs j) p.2 (zs (j + 1))))).comp
      ((hY j).prodMk (hY (j + 1))))

theorem gint {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Ka Kb : S → S → ℝ) (hKa : ∀ a b, 0 ≤ Ka a b) (hKb : ∀ a b, 0 ≤ Kb a b)
    (Q : S → S → S → S → ℝ)
    (hmarg : ∀ x z z', ∑' x', ENNReal.ofReal (Ka x x') * ENNReal.ofReal (Q x z x' z')
      = ENNReal.ofReal (Kb z z'))
    (z₀ : S) (Y : ℕ → Ω → S) (hY : ∀ n, Measurable (Y n))
    (hcyl : ∀ (n : ℕ) (zs : ℕ → S), P {ω | ∀ j ≤ n, Y j ω = zs j} =
      ENNReal.ofReal ((if zs 0 = z₀ then 1 else 0) * ∏ j ∈ Finset.range n, Ka (zs j) (zs (j + 1))))
    (zs : ℕ → S) (n : ℕ) :
    ∫⁻ ω, gprod Q Y zs n ω ∂P = ENNReal.ofReal (∏ j ∈ Finset.range n, Kb (zs j) (zs (j + 1))) := by
  induction n with
  | zero => simp [gprod]
  | succ n ih =>
    have hL : ∀ ω, gprod Q Y zs (n + 1) ω = Hf Q zs n (pre Y n ω) (Y (n + 1) ω) := by
      intro ω
      unfold gprod Hf
      apply Finset.prod_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      have h1 : ext (pre Y n ω) (Y (n + 1) ω) j = Y j ω := ext_pre_le Y n ω _ j (by omega)
      have h2 : ext (pre Y n ω) (Y (n + 1) ω) (j + 1) = Y (j + 1) ω := by
        rcases Nat.lt_or_ge (j + 1) (n + 1) with h | h
        · exact ext_pre_le Y n ω _ (j + 1) (by omega)
        · have : j + 1 = n + 1 := by omega
          rw [this, ext_succ']
      rw [h1, h2]
    have hR : ∀ ω, ∑' x', ENNReal.ofReal (Ka (Y n ω) x') * Hf Q zs n (pre Y n ω) x'
        = gprod Q Y zs n ω * ENNReal.ofReal (Kb (zs n) (zs (n + 1))) := by
      intro ω
      have hp : ∀ x', Hf Q zs n (pre Y n ω) x'
          = gprod Q Y zs n ω * ENNReal.ofReal (Q (Y n ω) (zs n) x' (zs (n + 1))) := by
        intro x'
        unfold Hf gprod
        rw [Finset.prod_range_succ, ext_pre_le Y n ω x' n le_rfl, ext_succ']
        congr 1
        apply Finset.prod_congr rfl
        intro j hj
        rw [Finset.mem_range] at hj
        rw [ext_pre_le Y n ω x' j (by omega), ext_pre_le Y n ω x' (j + 1) (by omega)]
      rw [tsum_congr (fun x' => by rw [hp x']), ← hmarg, ← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro x'
      ring
    calc ∫⁻ ω, gprod Q Y zs (n + 1) ω ∂P
        = ∫⁻ ω, Hf Q zs n (pre Y n ω) (Y (n + 1) ω) ∂P := lintegral_congr hL
      _ = ∫⁻ ω, ∑' x', ENNReal.ofReal (Ka (Y n ω) x') * Hf Q zs n (pre Y n ω) x' ∂P :=
          markov_int P Ka hKa z₀ Y hY hcyl n (Hf Q zs n)
      _ = ∫⁻ ω, gprod Q Y zs n ω * ENNReal.ofReal (Kb (zs n) (zs (n + 1))) ∂P := lintegral_congr hR
      _ = ENNReal.ofReal (∏ j ∈ Finset.range (n + 1), Kb (zs j) (zs (j + 1))) := by
          rw [lintegral_mul_const _ (measurable_gprod Q Y hY zs n), ih, ← ENNReal.ofReal_mul
            (Finset.prod_nonneg (fun j _ => hKb _ _)), Finset.prod_range_succ]

/-- K3d-2b: cylinder law of the constructed chain `Z` on `Ω × E`. -/
theorem zcyl {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure E) [SFinite ν]
    (Ka Kb : S → S → ℝ) (hKa : ∀ a b, 0 ≤ Ka a b) (hKb : ∀ a b, 0 ≤ Kb a b)
    (Q : S → S → S → S → ℝ)
    (hmarg : ∀ x z z', ∑' x', ENNReal.ofReal (Ka x x') * ENNReal.ofReal (Q x z x' z')
      = ENNReal.ofReal (Kb z z'))
    (z₀ : S) (Y : ℕ → Ω → S) (hY : ∀ n, Measurable (Y n))
    (hcyl : ∀ (n : ℕ) (zs : ℕ → S), P {ω | ∀ j ≤ n, Y j ω = zs j} =
      ENNReal.ofReal ((if zs 0 = z₀ then 1 else 0) * ∏ j ∈ Finset.range n, Ka (zs j) (zs (j + 1))))
    (π : E → ℕ → S × S × S → S) (hπ : Measurable π)
    (hν : ∀ (n : ℕ) (r : ℕ → S × S × S) (zz : ℕ → S),
      ν (π ⁻¹' {g | ∀ j < n, g j (r j) = zz j})
        = ∏ j ∈ Finset.range n, ENNReal.ofReal (Q (r j).1 (r j).2.1 (r j).2.2 (zz j)))
    (n : ℕ) (zs : ℕ → S) :
    (P.prod ν) {p : Ω × E | ∀ j ≤ n, Zmap z₀ (fun k => Y k p.1) (π p.2) j = zs j}
      = ENNReal.ofReal ((if zs 0 = z₀ then 1 else 0) *
          ∏ j ∈ Finset.range n, Kb (zs j) (zs (j + 1))) := by
  have hF : Measurable (fun p : Ω × E => Zmap z₀ (fun k => Y k p.1) (π p.2)) :=
    (measurable_Zmap z₀).comp ((measurable_pi_lambda _
      (fun k => (hY k).comp measurable_fst)).prodMk (hπ.comp measurable_snd))
  have hA : MeasurableSet {p : Ω × E | ∀ j ≤ n, Zmap z₀ (fun k => Y k p.1) (π p.2) j = zs j} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      (measurableSet_singleton (zs j)).preimage ((measurable_pi_apply j).comp hF)
  rw [Measure.prod_apply hA]
  have hpre : ∀ ω, Prod.mk ω ⁻¹' {p : Ω × E | ∀ j ≤ n, Zmap z₀ (fun k => Y k p.1) (π p.2) j = zs j}
      = π ⁻¹' {g | ∀ j ≤ n, Zmap z₀ (fun k => Y k ω) g j = zs j} := fun ω => rfl
  by_cases h0 : zs 0 = z₀
  · have hsec : ∀ ω, ν (Prod.mk ω ⁻¹'
        {p : Ω × E | ∀ j ≤ n, Zmap z₀ (fun k => Y k p.1) (π p.2) j = zs j}) = gprod Q Y zs n ω := by
      intro ω
      rw [hpre ω, Zmap_set z₀ _ n zs h0]
      exact hν n (fun j => (Y j ω, zs j, Y (j + 1) ω)) (fun j => zs (j + 1))
    rw [lintegral_congr hsec, gint P Ka Kb hKa hKb Q hmarg z₀ Y hY hcyl zs n, if_pos h0, one_mul]
  · have hsec : ∀ ω, ν (Prod.mk ω ⁻¹'
        {p : Ω × E | ∀ j ≤ n, Zmap z₀ (fun k => Y k p.1) (π p.2) j = zs j}) = 0 := by
      intro ω
      rw [hpre ω, Zmap_set_empty z₀ _ n zs h0, Set.preimage_empty, measure_empty]
    rw [lintegral_congr hsec, lintegral_zero, if_neg h0, zero_mul, ENNReal.ofReal_zero]

/-- The law of the random maps for one `N`: finite-dimensional formula. -/
theorem nu1_formula (Q : S → S → S → S → ℝ)
    [hQ : ∀ r : S × S × S, IsProbabilityMeasure (vecMeasure (Q r.1 r.2.1 r.2.2))]
    (n : ℕ) (r : ℕ → S × S × S) (zz : ℕ → S) :
    Measure.infinitePi (fun _ : ℕ => Measure.infinitePi
        (fun r : S × S × S => vecMeasure (Q r.1 r.2.1 r.2.2)))
      {g : ℕ → S × S × S → S | ∀ j < n, g j (r j) = zz j}
      = ∏ j ∈ Finset.range n, ENNReal.ofReal (Q (r j).1 (r j).2.1 (r j).2.2 (zz j)) := by
  have hset : {g : ℕ → S × S × S → S | ∀ j < n, g j (r j) = zz j}
      = Set.pi (Finset.range n : Set ℕ) (fun j => {h : S × S × S → S | h (r j) = zz j}) := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_pi, Finset.mem_coe, Finset.mem_range]
  rw [hset, Measure.infinitePi_pi _ (t := fun j => {h : S × S × S → S | h (r j) = zz j}) (fun j _ =>
    (measurableSet_singleton (zz j)).preimage (measurable_pi_apply (r j)))]
  apply Finset.prod_congr rfl
  intro j _
  have : {h : S × S × S → S | h (r j) = zz j} = (fun h : S × S × S → S => h (r j)) ⁻¹' {zz j} := rfl
  rw [this, ← Measure.map_apply (measurable_pi_apply (r j)) (measurableSet_singleton _),
    Measure.infinitePi_map_eval, vecMeasure_singleton]

/-- The nested law over all `N`, projected to coordinate `N`. -/
theorem nu_formula {T : ℕ → Type} [∀ N, MeasurableSpace (T N)] [∀ N, Countable (T N)]
    [∀ N, MeasurableSingletonClass (T N)] [∀ N, DecidableEq (T N)]
    (Q : ∀ N, T N → T N → T N → T N → ℝ)
    [hQ : ∀ N, ∀ r : T N × T N × T N, IsProbabilityMeasure (vecMeasure (Q N r.1 r.2.1 r.2.2))]
    (N n : ℕ) (r : ℕ → T N × T N × T N) (zz : ℕ → T N) :
    Measure.infinitePi (fun N => Measure.infinitePi (fun _ : ℕ => Measure.infinitePi
        (fun r : T N × T N × T N => vecMeasure (Q N r.1 r.2.1 r.2.2))))
      ((fun e => e N) ⁻¹' {g : ℕ → T N × T N × T N → T N | ∀ j < n, g j (r j) = zz j})
      = ∏ j ∈ Finset.range n, ENNReal.ofReal (Q N (r j).1 (r j).2.1 (r j).2.2 (zz j)) := by
  have hmeas : MeasurableSet {g : ℕ → T N × T N × T N → T N | ∀ j < n, g j (r j) = zz j} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      (measurableSet_singleton (zz j)).preimage
        ((measurable_pi_apply (r j)).comp (measurable_pi_apply j))
  rw [← Measure.map_apply (measurable_pi_apply N) hmeas, Measure.infinitePi_map_eval]
  exact nu1_formula (Q N) n r zz

end SC77K3D3

/-! K3d-2c: the coupled `piRoute` chain on `Ω × E`. Given the JSQ(d) chain `Y` (with clocks `τ`)
on `Ω`, the chain `Z N n (ω, e) = Zmap (z₀ N) (Y N · ω) (e N) n` driven by independent random
maps `e` with law `nu` is a `piRoute (jsqdAssign d)` load-balancing process with clocks `τ ∘ fst`. -/

namespace SC77K3D4

open StrictCompatLB.MeanField SC77K3D SC77K3D3

section Assemble

variable (lam : ℝ) (d : ℕ) (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N)))

lemma jr_nonneg (N : ℕ) (w : Fin (M N)) (z : Fin N → ℕ) (v : Fin N) :
    0 ≤ jsqdRoute M G N d w z v := by
  unfold jsqdRoute
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply Finset.sum_nonneg
  intro U _
  split_ifs
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · exact le_refl 0

lemma pr_nonneg (N : ℕ) (w : Fin (M N)) (z : Fin N → ℕ) (v : Fin N) :
    0 ≤ piRoute M G N (jsqdAssign d) w z v := by
  by_cases hv : v ∈ nbrW M G N w
  · rw [SC77K3A.pr_level M G N d w z v hv]
    unfold SC77K3A.Gq
    apply div_nonneg _ (Nat.cast_nonneg _)
    apply sub_nonneg.mpr
    apply pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    have hA : SC77K3A.Acnt M G N z w (z v + 1) ≤ SC77K3A.Acnt M G N z w (z v) :=
      Finset.card_le_card (fun u hu => by
        simp only [Finset.mem_filter] at hu ⊢
        exact ⟨hu.1, by omega⟩)
    exact_mod_cast hA
  · unfold piRoute
    rw [if_neg hv]

lemma hs_eq (hd : 1 ≤ d) (N : ℕ) (w : Fin (M N)) (x z : Fin N → ℕ) :
    ∑ v, jsqdRoute M G N d w x v = ∑ v, piRoute M G N (jsqdAssign d) w z v := by
  by_cases hn : 1 ≤ (nbrW M G N w).card
  · rw [SC77K3A.sum_jr M G N d hd w x hn, SC77K3A.sum_pr M G N d hd w z hn]
  · have he : ∀ v, v ∉ nbrW M G N w := by
      intro v hv
      exact hn (Finset.card_pos.mpr ⟨v, hv⟩)
    rw [Finset.sum_eq_zero (fun v _ => SC77K3A.jr_out M G N d w x v (he v)),
      Finset.sum_eq_zero (fun v _ => by unfold piRoute; rw [if_neg (he v)])]

lemma lbK_nonneg (hlam : 0 ≤ lam) (N : ℕ) (route : Fin (M N) → (Fin N → ℕ) → Fin N → ℝ)
    (hr : ∀ w z v, 0 ≤ route w z v) (z z' : Fin N → ℕ) : 0 ≤ lbKernel lam M N route z z' := by
  unfold lbKernel
  have hI : ∀ (P : Prop) [Decidable P], (0 : ℝ) ≤ if P then 1 else 0 := by
    intro P _; split_ifs <;> norm_num
  apply add_nonneg
  · apply mul_nonneg (mul_nonneg (div_nonneg hlam (by linarith)) (by positivity))
    exact Finset.sum_nonneg fun w _ => Finset.sum_nonneg fun v _ => mul_nonneg (hr w z v) (hI _)
  · apply mul_nonneg (mul_nonneg (div_nonneg zero_le_one (by linarith)) (by positivity))
    exact Finset.sum_nonneg fun v _ => hI _

/-- The conditional kernel of the `piRoute` chain given the JSQ(d) step. -/
noncomputable def QN (N : ℕ) : (Fin N → ℕ) → (Fin N → ℕ) → (Fin N → ℕ) → (Fin N → ℕ) → ℝ :=
  SC77K3D2.Q lam M N (jsqdRoute M G N d) (piRoute M G N (jsqdAssign d))

lemma QN_prob (hlam : 0 ≤ lam) (hd : 1 ≤ d) (N : ℕ)
    (r : (Fin N → ℕ) × (Fin N → ℕ) × (Fin N → ℕ)) :
    IsProbabilityMeasure (vecMeasure (QN lam d M G N r.1 r.2.1 r.2.2)) :=
  vecMeasure_isProb _
    (fun z' => SC77K3D2.Q_nonneg lam M N _ _ hlam (jr_nonneg d M G N) (pr_nonneg d M G N) _ _ _ z')
    (SC77K3D2.Q_hasSum lam M N _ _ (hs_eq d M G hd N) _ _ _)

/-- The space of random maps, one family per `N`. -/
abbrev EE := (N : ℕ) → ℕ → ((Fin N → ℕ) × (Fin N → ℕ) × (Fin N → ℕ) → (Fin N → ℕ))

/-- The law of the random maps. -/
noncomputable def nu (hlam : 0 ≤ lam) (hd : 1 ≤ d) : Measure EE :=
  haveI : ∀ N (r : (Fin N → ℕ) × (Fin N → ℕ) × (Fin N → ℕ)),
      IsProbabilityMeasure (vecMeasure (QN lam d M G N r.1 r.2.1 r.2.2)) :=
    fun N r => QN_prob lam d M G hlam hd N r
  Measure.infinitePi (fun N => Measure.infinitePi (fun _ : ℕ => Measure.infinitePi
    (fun r : (Fin N → ℕ) × (Fin N → ℕ) × (Fin N → ℕ) => vecMeasure (QN lam d M G N r.1 r.2.1 r.2.2))))

lemma nu_prob (hlam : 0 ≤ lam) (hd : 1 ≤ d) : IsProbabilityMeasure (nu lam d M G hlam hd) := by
  haveI : ∀ N (r : (Fin N → ℕ) × (Fin N → ℕ) × (Fin N → ℕ)),
      IsProbabilityMeasure (vecMeasure (QN lam d M G N r.1 r.2.1 r.2.2)) :=
    fun N r => QN_prob lam d M G hlam hd N r
  unfold nu
  infer_instance

lemma nu_cyl (hlam : 0 ≤ lam) (hd : 1 ≤ d) (N n : ℕ)
    (r : ℕ → (Fin N → ℕ) × (Fin N → ℕ) × (Fin N → ℕ)) (zz : ℕ → Fin N → ℕ) :
    nu lam d M G hlam hd ((fun e : EE => e N) ⁻¹'
        {g : ℕ → (Fin N → ℕ) × (Fin N → ℕ) × (Fin N → ℕ) → (Fin N → ℕ) | ∀ j < n, g j (r j) = zz j})
      = ∏ j ∈ Finset.range n, ENNReal.ofReal (QN lam d M G N (r j).1 (r j).2.1 (r j).2.2 (zz j)) := by
  haveI : ∀ N (r : (Fin N → ℕ) × (Fin N → ℕ) × (Fin N → ℕ)),
      IsProbabilityMeasure (vecMeasure (QN lam d M G N r.1 r.2.1 r.2.2)) :=
    fun N r => QN_prob lam d M G hlam hd N r
  unfold nu
  exact nu_formula (T := fun N => Fin N → ℕ) (fun N => QN lam d M G N) N n r zz

/-- The coupled chain. -/
def Zc {Ω : Type} (z₀ : (N : ℕ) → Fin N → ℕ) (Y : (N : ℕ) → ℕ → Ω → (Fin N → ℕ)) (N n : ℕ)
    (p : Ω × EE) : Fin N → ℕ :=
  Zmap (z₀ N) (fun k => Y N k p.1) (p.2 N) n

theorem Z_isLB (hlam : 0 ≤ lam) (hd : 1 ≤ d) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (z₀ : (N : ℕ) → Fin N → ℕ) (Y : (N : ℕ) → ℕ → Ω → (Fin N → ℕ)) (τ : ℕ → ℕ → Ω → ℝ) (N : ℕ)
    (hY : IsLBProcess P lam M N (jsqdRoute M G N d) (z₀ N) (Y N) (τ N)) :
    IsLBProcess (P.prod (nu lam d M G hlam hd)) lam M N (piRoute M G N (jsqdAssign d)) (z₀ N)
      (Zc z₀ Y N) (fun k p => τ N k p.1) := by
  obtain ⟨hP, hYm, hcyl, hτm, hind, hlaw, hYτ⟩ := hY
  haveI := hP
  haveI := nu_prob lam d M G hlam hd
  have hfst : ∀ B : Set Ω, (P.prod (nu lam d M G hlam hd)) (Prod.fst ⁻¹' B) = P B := by
    intro B
    rw [← Set.prod_univ, Measure.prod_prod, measure_univ, mul_one]
  have hZm : Measurable (fun p : Ω × EE => Zmap (z₀ N) (fun k => Y N k p.1) (p.2 N)) :=
    (measurable_Zmap (z₀ N)).comp ((measurable_pi_lambda _ (fun k => (hYm k).comp
      measurable_fst)).prodMk ((measurable_pi_apply N).comp measurable_snd))
  have hYs : Measurable (fun ω n => Y N n ω) := measurable_pi_lambda _ hYm
  have hTs : Measurable (fun ω k => τ N k ω) := measurable_pi_lambda _ hτm
  refine ⟨inferInstance, fun n => (measurable_pi_apply n).comp hZm, ?_,
    fun k => (hτm k).comp measurable_fst, ?_, ?_, ?_⟩
  · intro n zs
    exact zcyl P (nu lam d M G hlam hd) (lbKernel lam M N (jsqdRoute M G N d))
      (lbKernel lam M N (piRoute M G N (jsqdAssign d)))
      (lbK_nonneg lam M hlam N _ (jr_nonneg d M G N)) (lbK_nonneg lam M hlam N _ (pr_nonneg d M G N))
      (QN lam d M G N)
      (fun x z z' => SC77K3D2.marg_ennreal lam M N _ _ hlam (jr_nonneg d M G N) (pr_nonneg d M G N)
        (hs_eq d M G hd N) x z z')
      (z₀ N) (Y N) hYm hcyl (fun e => e N) (measurable_pi_apply N)
      (fun n r zz => nu_cyl lam d M G hlam hd N n r zz) n zs
  · rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at hind ⊢
    intro s sets hsets
    have h1 : (⋂ i ∈ s, (fun p : Ω × EE => τ N i p.1) ⁻¹' sets i)
        = Prod.fst ⁻¹' (⋂ i ∈ s, τ N i ⁻¹' sets i) := by
      ext p; simp
    rw [h1, hfst, hind s hsets]
    exact Finset.prod_congr rfl (fun i _ => (hfst (τ N i ⁻¹' sets i)).symm)
  · intro k
    show Measure.map (τ N k ∘ Prod.fst) (P.prod (nu lam d M G hlam hd)) = _
    rw [← Measure.map_map (hτm k) measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]
    exact hlaw k
  · classical
    rw [indepFun_iff_measure_inter_preimage_eq_mul]
    intro A B hA hB
    have hZA' : MeasurableSet ((fun p : Ω × EE => fun n => Zc z₀ Y N n p) ⁻¹' A) := hZm hA
    have hTB' : MeasurableSet ((fun p : Ω × EE => fun k => τ N k p.1) ⁻¹' B) :=
      (hTs.comp measurable_fst) hB
    set ν := nu lam d M G hlam hd with hν
    have hsm : MeasurableSet {q : (ℕ → Fin N → ℕ) × EE | Zmap (z₀ N) q.1 (q.2 N) ∈ A} :=
      hA.preimage ((measurable_Zmap (z₀ N)).comp (measurable_fst.prodMk
        ((measurable_pi_apply N).comp measurable_snd)))
    have hh : Measurable (fun y : ℕ → Fin N → ℕ =>
        ν (Prod.mk y ⁻¹' {q : (ℕ → Fin N → ℕ) × EE | Zmap (z₀ N) q.1 (q.2 N) ∈ A})) :=
      measurable_measure_prodMk_left hsm
    have hsec : ∀ ω, ν (Prod.mk ω ⁻¹' ((fun p : Ω × EE => fun n => Zc z₀ Y N n p) ⁻¹' A ∩
        (fun p : Ω × EE => fun k => τ N k p.1) ⁻¹' B))
        = ν (Prod.mk (fun n => Y N n ω) ⁻¹'
            {q : (ℕ → Fin N → ℕ) × EE | Zmap (z₀ N) q.1 (q.2 N) ∈ A})
          * B.indicator 1 (fun k => τ N k ω) := by
      intro ω
      by_cases hb : (fun k => τ N k ω) ∈ B
      · rw [Set.indicator_apply, if_pos hb, Pi.one_apply, mul_one]
        congr 1
        ext e
        exact ⟨fun h => h.1, fun h => ⟨h, hb⟩⟩
      · rw [Set.indicator_apply, if_neg hb, mul_zero]
        have : Prod.mk ω ⁻¹' ((fun p : Ω × EE => fun n => Zc z₀ Y N n p) ⁻¹' A ∩
            (fun p : Ω × EE => fun k => τ N k p.1) ⁻¹' B) = ∅ := by
          ext e
          exact ⟨fun h => hb h.2, fun h => h.elim⟩
        rw [this, measure_empty]
    have hmul := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun (μ := P)
      (hh.comp hYs) ((measurable_one.indicator hB).comp hTs) (hYτ.comp hh (measurable_one.indicator hB))
    have hZA : (P.prod ν) ((fun p : Ω × EE => fun n => Zc z₀ Y N n p) ⁻¹' A)
        = ∫⁻ ω, ν (Prod.mk (fun n => Y N n ω) ⁻¹'
            {q : (ℕ → Fin N → ℕ) × EE | Zmap (z₀ N) q.1 (q.2 N) ∈ A}) ∂P := by
      rw [Measure.prod_apply hZA']
      rfl
    have hTB : (P.prod ν) ((fun p : Ω × EE => fun k => τ N k p.1) ⁻¹' B)
        = ∫⁻ ω, B.indicator 1 (fun k => τ N k ω) ∂P := by
      rw [show (fun p : Ω × EE => fun k => τ N k p.1) ⁻¹' B
          = Prod.fst ⁻¹' ((fun ω k => τ N k ω) ⁻¹' B) from rfl, hfst,
        ← Measure.map_apply hTs hB, ← lintegral_indicator_one hB,
        lintegral_map (measurable_one.indicator hB) hTs]
    rw [hZA, hTB, Measure.prod_apply (hZA'.inter hTB'),
      lintegral_congr hsec]
    exact hmul

end Assemble

end SC77K3D4

/-! K3e (a): one-step drift of the l1 distance between the coupled chains (session 11). -/

namespace SC77K3EA

open StrictCompatLB.MeanField SC77K3D2

/-- l1 distance between two occupancy vectors. -/
noncomputable def Dist {N : ℕ} (x z : Fin N → ℕ) : ℝ := ∑ v, |(x v : ℝ) - (z v : ℝ)|

lemma Dist_nonneg {N : ℕ} (x z : Fin N → ℕ) : 0 ≤ Dist x z :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

lemma Dist_self {N : ℕ} (x : Fin N → ℕ) : Dist x x = 0 := by
  simp [Dist]

lemma nat_pred_abs (a b : ℕ) :
    |((a - 1 : ℕ) : ℝ) - ((b - 1 : ℕ) : ℝ)| ≤ |(a : ℝ) - (b : ℝ)| := by
  have key : ∀ c : ℕ, (1 ≤ c ∧ ((c - 1 : ℕ) : ℝ) = (c : ℝ) - 1) ∨ (c = 0) := by
    intro c
    rcases Nat.eq_zero_or_pos c with h | h
    · right; exact h
    · left; exact ⟨h, by rw [Nat.cast_sub h]; simp⟩
  rcases key a with ⟨ha1, ha⟩ | ha0 <;> rcases key b with ⟨hb1, hb⟩ | hb0
  · rw [ha, hb, show (a : ℝ) - 1 - ((b : ℝ) - 1) = (a : ℝ) - b by ring]
  · subst hb0
    have : (1 : ℝ) ≤ a := by exact_mod_cast ha1
    rw [ha]
    simp only [Nat.zero_sub, Nat.cast_zero, sub_zero]
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · subst ha0
    have : (1 : ℝ) ≤ b := by exact_mod_cast hb1
    rw [hb]
    simp only [Nat.zero_sub, Nat.cast_zero, zero_sub, abs_neg]
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · subst ha0; subst hb0; simp

lemma Dist_depart_le {N : ℕ} (x z : Fin N → ℕ) (v : Fin N) :
    Dist (depart x v) (depart z v) ≤ Dist x z := by
  unfold Dist
  apply Finset.sum_le_sum
  intro u _
  by_cases h : u = v
  · subst h
    simp only [depart, Function.update_self]
    exact nat_pred_abs _ _
  · simp only [depart, Function.update_of_ne h]
    exact le_refl _

lemma arrive_cast {N : ℕ} (x : Fin N → ℕ) (v u : Fin N) :
    ((arrive x v u : ℕ) : ℝ) = (x u : ℝ) + (if u = v then 1 else 0) := by
  by_cases h : u = v
  · subst h
    simp [arrive, Function.update_self]
  · simp [arrive, Function.update_of_ne h, h]

lemma Dist_arrive_same {N : ℕ} (x z : Fin N → ℕ) (v : Fin N) :
    Dist (arrive x v) (arrive z v) = Dist x z := by
  unfold Dist
  apply Finset.sum_congr rfl
  intro u _
  rw [arrive_cast, arrive_cast]
  congr 1
  ring

lemma Dist_arrive_le {N : ℕ} (x z : Fin N → ℕ) (v v' : Fin N) :
    Dist (arrive x v) (arrive z v') ≤ Dist x z + 2 := by
  unfold Dist
  have h : ∀ u : Fin N, |((arrive x v u : ℕ) : ℝ) - ((arrive z v' u : ℕ) : ℝ)|
      ≤ |(x u : ℝ) - (z u : ℝ)| + ((if u = v then (1 : ℝ) else 0) + (if u = v' then 1 else 0)) := by
    intro u
    rw [arrive_cast, arrive_cast]
    have h1 : (0 : ℝ) ≤ (if u = v then 1 else 0) := by split_ifs <;> norm_num
    have h2 : (0 : ℝ) ≤ (if u = v' then 1 else 0) := by split_ifs <;> norm_num
    have h3 := le_abs_self ((x u : ℝ) - (z u : ℝ))
    have h4 := neg_abs_le ((x u : ℝ) - (z u : ℝ))
    rw [abs_le]
    constructor <;> linarith
  calc ∑ u, |((arrive x v u : ℕ) : ℝ) - ((arrive z v' u : ℕ) : ℝ)|
      ≤ ∑ u, (|(x u : ℝ) - (z u : ℝ)|
          + ((if u = v then (1 : ℝ) else 0) + (if u = v' then 1 else 0))) :=
        Finset.sum_le_sum (fun u _ => h u)
    _ = ∑ u, |(x u : ℝ) - (z u : ℝ)| + 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
          Finset.sum_ite_eq']
        simp only [Finset.mem_univ, if_true]
        ring

section Drift

variable (lam : ℝ) (M : ℕ → ℕ) (N : ℕ) (ra rb : Fin (M N) → (Fin N → ℕ) → Fin N → ℝ)

lemma atom_mul {α : Type*} (c : ℝ) (hc : 0 ≤ c) (a t : α) (F : α → ℝ≥0∞) [Decidable (a = t)] :
    ENNReal.ofReal (c * (if a = t then 1 else 0)) * F a
      = if a = t then ENNReal.ofReal c * F t else 0 := by
  by_cases h : a = t
  · subst h; simp
  · simp [h]

lemma ite2 {α β : Type*} (x' a : α) (z' b : β) [Decidable (x' = a)] [Decidable (z' = b)]
    [Decidable ((x', z') = (a, b))] :
    ((if x' = a then (1 : ℝ) else 0) * (if z' = b then 1 else 0))
      = if (x', z') = (a, b) then 1 else 0 := by
  by_cases h1 : x' = a <;> by_cases h2 : z' = b <;> simp [h1, h2]

/-- Expansion of a one-step `Kc`-expectation into its finitely many atoms. -/
theorem Kc_tsum (hlam : 0 ≤ lam) (hra : ∀ w x v, 0 ≤ ra w x v) (hrb : ∀ w x v, 0 ≤ rb w x v)
    (x z : Fin N → ℕ) (F : (Fin N → ℕ) × (Fin N → ℕ) → ℝ≥0∞) :
    ∑' p', ENNReal.ofReal (Kc lam M N ra rb (x, z) p') * F p'
      = ENNReal.ofReal (lam / (lam + 1) * (1 / (M N : ℝ))) *
          ∑ w : Fin (M N), ∑ v : Fin N, ∑ v' : Fin N,
            ENNReal.ofReal (cpl (ra w x) (rb w z) v v') * F (arrive x v, arrive z v')
        + ENNReal.ofReal (1 / (lam + 1) * (1 / (N : ℝ))) *
          ∑ v : Fin N, F (depart x v, depart z v) := by
  have hc : ∀ w v v', 0 ≤ cpl (ra w x) (rb w z) v v' :=
    fun w v v' => cpl_nonneg _ _ (hra w x) (hrb w z) v v'
  have hA : 0 ≤ lam / (lam + 1) * (1 / (M N : ℝ)) := by positivity
  have hB : 0 ≤ 1 / (lam + 1) * (1 / (N : ℝ)) := by positivity
  have hI : ∀ (P : Prop) [Decidable P], (0 : ℝ) ≤ if P then 1 else 0 := by
    intro P _; split_ifs <;> norm_num
  have hpt : ∀ p' : (Fin N → ℕ) × (Fin N → ℕ),
      ENNReal.ofReal (Kc lam M N ra rb (x, z) p') * F p'
        = ENNReal.ofReal (lam / (lam + 1) * (1 / (M N : ℝ))) *
            ∑ w : Fin (M N), ∑ v : Fin N, ∑ v' : Fin N,
              (if p' = (arrive x v, arrive z v') then
                ENNReal.ofReal (cpl (ra w x) (rb w z) v v') * F (arrive x v, arrive z v') else 0)
          + ENNReal.ofReal (1 / (lam + 1) * (1 / (N : ℝ))) *
            ∑ v : Fin N, (if p' = (depart x v, depart z v) then
                ENNReal.ofReal 1 * F (depart x v, depart z v) else 0) := by
    rintro ⟨x', z'⟩
    unfold Kc
    simp only [mul_assoc, ite2]
    have hs1 : 0 ≤ ∑ w : Fin (M N), ∑ v : Fin N, ∑ v' : Fin N,
        cpl (ra w x) (rb w z) v v' * (if (x', z') = (arrive x v, arrive z v') then (1 : ℝ) else 0) :=
      Finset.sum_nonneg fun w _ => Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun v' _ =>
        mul_nonneg (hc w v v') (hI _)
    have hs2 : 0 ≤ ∑ v : Fin N, (if (x', z') = (depart x v, depart z v) then (1 : ℝ) else 0) :=
      Finset.sum_nonneg fun v _ => hI _
    rw [← mul_assoc, ← mul_assoc, ENNReal.ofReal_add (mul_nonneg hA hs1) (mul_nonneg hB hs2),
      add_mul, ENNReal.ofReal_mul hA, ENNReal.ofReal_mul hB, mul_assoc, mul_assoc]
    congr 2
    · rw [ENNReal.ofReal_sum_of_nonneg (fun w _ => Finset.sum_nonneg fun v _ =>
          Finset.sum_nonneg fun v' _ => mul_nonneg (hc w v v') (hI _)), Finset.sum_mul]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [ENNReal.ofReal_sum_of_nonneg (fun v _ =>
          Finset.sum_nonneg fun v' _ => mul_nonneg (hc w v v') (hI _)), Finset.sum_mul]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [ENNReal.ofReal_sum_of_nonneg (fun v' _ => mul_nonneg (hc w v v') (hI _)),
        Finset.sum_mul]
      refine Finset.sum_congr rfl fun v' _ => ?_
      exact atom_mul _ (hc w v v') _ _ F
    · rw [ENNReal.ofReal_sum_of_nonneg (fun v _ => hI _), Finset.sum_mul]
      refine Finset.sum_congr rfl fun v _ => ?_
      have := atom_mul 1 zero_le_one (x', z') (depart x v, depart z v) F
      rw [one_mul] at this
      exact this
  simp_rw [hpt]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
  congr 2
  · rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    refine Finset.sum_congr rfl fun v' _ => ?_
    exact tsum_ite_eq _ _
  · rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [tsum_ite_eq, ENNReal.ofReal_one, one_mul]

/-- K3e (a): the expected positive increment of `Dist` under one coupled step is at most
`2 λ/(λ+1) (1/M) Σ_w Σ_v |ra w x v - rb w z v|`. -/
theorem drift_le (hlam : 0 ≤ lam) (hra : ∀ w x v, 0 ≤ ra w x v) (hrb : ∀ w x v, 0 ≤ rb w x v)
    (hs : ∀ w x z, ∑ v, ra w x v = ∑ v, rb w z v) (x z : Fin N → ℕ) :
    ∑' p', ENNReal.ofReal (Kc lam M N ra rb (x, z) p') * ENNReal.ofReal (Dist p'.1 p'.2 - Dist x z)
      ≤ ENNReal.ofReal (lam / (lam + 1) * (1 / (M N : ℝ)) *
          ∑ w : Fin (M N), 2 * ∑ v : Fin N, |ra w x v - rb w z v|) := by
  have hc : ∀ w v v', 0 ≤ cpl (ra w x) (rb w z) v v' :=
    fun w v v' => cpl_nonneg _ _ (hra w x) (hrb w z) v v'
  have hA : 0 ≤ lam / (lam + 1) * (1 / (M N : ℝ)) := by positivity
  rw [Kc_tsum lam M N ra rb hlam hra hrb x z (fun p' => ENNReal.ofReal (Dist p'.1 p'.2 - Dist x z))]
  have hdep : ∀ v : Fin N, ENNReal.ofReal (Dist (depart x v) (depart z v) - Dist x z) = 0 := by
    intro v
    rw [ENNReal.ofReal_eq_zero]
    linarith [Dist_depart_le x z v]
  simp only [hdep, Finset.sum_const_zero, mul_zero, add_zero]
  rw [ENNReal.ofReal_mul hA, ENNReal.ofReal_sum_of_nonneg (fun w _ => by positivity)]
  gcongr with w _
  have hterm : ∀ v v', ENNReal.ofReal (cpl (ra w x) (rb w z) v v')
      * ENNReal.ofReal (Dist (arrive x v) (arrive z v') - Dist x z)
        ≤ ENNReal.ofReal (2 * (if v = v' then 0 else cpl (ra w x) (rb w z) v v')) := by
    intro v v'
    rw [← ENNReal.ofReal_mul (hc w v v')]
    apply ENNReal.ofReal_le_ofReal
    by_cases h : v = v'
    · subst h
      rw [Dist_arrive_same]
      simp
    · rw [if_neg h]
      have := Dist_arrive_le x z v v'
      nlinarith [hc w v v']
  have hnn : ∀ v v', 0 ≤ 2 * (if v = v' then 0 else cpl (ra w x) (rb w z) v v') := by
    intro v v'
    split_ifs
    · norm_num
    · linarith [hc w v v']
  calc ∑ v : Fin N, ∑ v' : Fin N, ENNReal.ofReal (cpl (ra w x) (rb w z) v v')
        * ENNReal.ofReal (Dist (arrive x v) (arrive z v') - Dist x z)
      ≤ ∑ v : Fin N, ∑ v' : Fin N,
          ENNReal.ofReal (2 * (if v = v' then 0 else cpl (ra w x) (rb w z) v v')) := by
        gcongr with v _ v' _
        exact hterm v v'
    _ = ENNReal.ofReal (∑ v : Fin N, ∑ v' : Fin N,
          2 * (if v = v' then 0 else cpl (ra w x) (rb w z) v v')) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun v _ => Finset.sum_nonneg fun v' _ => hnn v v')]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [ENNReal.ofReal_sum_of_nonneg (fun v' _ => hnn v v')]
    _ ≤ ENNReal.ofReal (2 * ∑ v : Fin N, |ra w x v - rb w z v|) := by
        apply ENNReal.ofReal_le_ofReal
        simp_rw [← Finset.mul_sum]
        have := cpl_off (ra w x) (rb w z) (hs w x z)
        linarith

end Drift

end SC77K3EA

/-! K3e (a2): split the routing discrepancy into the JSQ(d)-vs-assignment error and the
assignment-law Lipschitz term (session 11). -/

namespace SC77K3EB

open StrictCompatLB.MeanField SC77K3D2 SC77K3EA

theorem route_split (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N d : ℕ)
    (hd : 1 ≤ d) (w : Fin (M N)) (x z : Fin N → ℕ) :
    ∑ v : Fin N, |jsqdRoute M G N d w x v - piRoute M G N (jsqdAssign d) w z v|
      ≤ 2 * (d : ℝ) ^ 3 / (nbrW M G N w).card
        + (2 * (d : ℝ) ^ 2 + 2 * d) *
          (((nbrW M G N w ∩ Finset.univ.filter (fun v => x v ≠ z v)).card : ℝ)
            / (nbrW M G N w).card) := by
  calc ∑ v : Fin N, |jsqdRoute M G N d w x v - piRoute M G N (jsqdAssign d) w z v|
      ≤ ∑ v : Fin N, (|jsqdRoute M G N d w x v - piRoute M G N (jsqdAssign d) w x v|
          + |piRoute M G N (jsqdAssign d) w x v - piRoute M G N (jsqdAssign d) w z v|) :=
        Finset.sum_le_sum fun v _ => abs_sub_le _ _ _
    _ = ∑ v : Fin N, |jsqdRoute M G N d w x v - piRoute M G N (jsqdAssign d) w x v|
          + ∑ v : Fin N, |piRoute M G N (jsqdAssign d) w x v
              - piRoute M G N (jsqdAssign d) w z v| := Finset.sum_add_distrib
    _ ≤ _ := add_le_add (SC77K3A.tv_jsqd M G N d hd w x) (SC77K3.tv_piRoute M G N d x z w)

theorem card_diff_le {N : ℕ} (x z : Fin N → ℕ) :
    ((Finset.univ.filter (fun v => x v ≠ z v)).card : ℝ) ≤ Dist x z := by
  have h1 : ∀ v ∈ Finset.univ.filter (fun v => x v ≠ z v),
      (1 : ℝ) ≤ |(x v : ℝ) - (z v : ℝ)| := by
    intro v hv
    rw [Finset.mem_filter] at hv
    rcases lt_or_gt_of_ne hv.2 with h | h
    · have h' : x v + 1 ≤ z v := h
      have : (x v : ℝ) + 1 ≤ z v := by exact_mod_cast h'
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith
    · have h' : z v + 1 ≤ x v := h
      have : (z v : ℝ) + 1 ≤ x v := by exact_mod_cast h'
      rw [abs_of_nonneg (by linarith)]
      linarith
  calc ((Finset.univ.filter (fun v => x v ≠ z v)).card : ℝ)
      = ∑ v ∈ Finset.univ.filter (fun v => x v ≠ z v), (1 : ℝ) := by simp
    _ ≤ ∑ v ∈ Finset.univ.filter (fun v => x v ≠ z v), |(x v : ℝ) - (z v : ℝ)| :=
        Finset.sum_le_sum h1
    _ ≤ Dist x z :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => abs_nonneg _)

/-- K3e (a) for the concrete routes: one-step expected positive increment of `Dist`. -/
theorem drift_jsqd (lam : ℝ) (hlam : 0 ≤ lam) (d : ℕ) (hd : 1 ≤ d) (M : ℕ → ℕ)
    (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ)
    (hra : ∀ w x v, 0 ≤ jsqdRoute M G N d w x v)
    (hrb : ∀ w x v, 0 ≤ piRoute M G N (jsqdAssign d) w x v)
    (hs : ∀ w x z, ∑ v, jsqdRoute M G N d w x v = ∑ v, piRoute M G N (jsqdAssign d) w z v)
    (x z : Fin N → ℕ) :
    ∑' p', ENNReal.ofReal (Kc lam M N (jsqdRoute M G N d) (piRoute M G N (jsqdAssign d))
        (x, z) p') * ENNReal.ofReal (Dist p'.1 p'.2 - Dist x z)
      ≤ ENNReal.ofReal (lam / (lam + 1) * (1 / (M N : ℝ)) *
          ∑ w : Fin (M N), 2 * (2 * (d : ℝ) ^ 3 / (nbrW M G N w).card
            + (2 * (d : ℝ) ^ 2 + 2 * d) *
              (((nbrW M G N w ∩ Finset.univ.filter (fun v => x v ≠ z v)).card : ℝ)
                / (nbrW M G N w).card))) := by
  have hA : 0 ≤ lam / (lam + 1) * (1 / (M N : ℝ)) := by positivity
  refine (drift_le lam M N _ _ hlam hra hrb hs x z).trans (ENNReal.ofReal_le_ofReal ?_)
  apply mul_le_mul_of_nonneg_left _ hA
  apply Finset.sum_le_sum
  intro w _
  have := route_split M G N d hd w x z
  linarith

end SC77K3EB

/-! K3e (b): the PAIR (Y, Z) on `Ω × E` is a Markov chain with kernel `Ka(x,x') Q(x,z,x',z')`,
the integral form of its one-step law, and the Gronwall bound for the positive increments. -/

namespace SC77K3EP

open SC77K3D SC77K3D3

section Pair

variable {S : Type} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S] [DecidableEq S]

/-- The coupled pair chain. -/
def W {Ω E : Type*} (Y : ℕ → Ω → S) (z₀ : S) (π : E → ℕ → S × S × S → S) (n : ℕ)
    (p : Ω × E) : S × S :=
  (Y n p.1, Zmap z₀ (fun k => Y k p.1) (π p.2) n)

/-- Pair kernel. -/
def K2 (Ka : S → S → ℝ) (Q : S → S → S → S → ℝ) (a b : S × S) : ℝ :=
  Ka a.1 b.1 * Q a.1 a.2 b.1 b.2

lemma measurable_W {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (Y : ℕ → Ω → S) (hY : ∀ n, Measurable (Y n)) (z₀ : S) (π : E → ℕ → S × S × S → S)
    (hπ : Measurable π) (n : ℕ) : Measurable (W Y z₀ π n) := by
  have hF : Measurable (fun p : Ω × E => Zmap z₀ (fun k => Y k p.1) (π p.2)) :=
    (measurable_Zmap z₀).comp ((measurable_pi_lambda _
      (fun k => (hY k).comp measurable_fst)).prodMk (hπ.comp measurable_snd))
  exact ((hY n).comp measurable_fst).prodMk ((measurable_pi_apply n).comp hF)

theorem pair_cyl {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] (P : Measure Ω)
    (ν : Measure E) [SFinite ν]
    (Ka : S → S → ℝ) (hKa : ∀ a b, 0 ≤ Ka a b)
    (Q : S → S → S → S → ℝ) (hQ : ∀ x z x' z', 0 ≤ Q x z x' z')
    (y₀ z₀ : S) (Y : ℕ → Ω → S) (hY : ∀ n, Measurable (Y n))
    (hcyl : ∀ (n : ℕ) (zs : ℕ → S), P {ω | ∀ j ≤ n, Y j ω = zs j} =
      ENNReal.ofReal ((if zs 0 = y₀ then 1 else 0) * ∏ j ∈ Finset.range n, Ka (zs j) (zs (j + 1))))
    (π : E → ℕ → S × S × S → S) (hπ : Measurable π)
    (hν : ∀ (n : ℕ) (r : ℕ → S × S × S) (zz : ℕ → S),
      ν (π ⁻¹' {g | ∀ j < n, g j (r j) = zz j})
        = ∏ j ∈ Finset.range n, ENNReal.ofReal (Q (r j).1 (r j).2.1 (r j).2.2 (zz j)))
    (n : ℕ) (ws : ℕ → S × S) :
    (P.prod ν) {p : Ω × E | ∀ j ≤ n, W Y z₀ π j p = ws j}
      = ENNReal.ofReal ((if ws 0 = (y₀, z₀) then 1 else 0) *
          ∏ j ∈ Finset.range n, K2 Ka Q (ws j) (ws (j + 1))) := by
  have hA : MeasurableSet {p : Ω × E | ∀ j ≤ n, W Y z₀ π j p = ws j} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      (measurableSet_singleton (ws j)).preimage (measurable_W Y hY z₀ π hπ j)
  have hB : MeasurableSet {ω | ∀ j ≤ n, Y j ω = (ws j).1} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      (measurableSet_singleton ((ws j).1)).preimage (hY j)
  rw [Measure.prod_apply hA]
  by_cases h0 : (ws 0).2 = z₀
  · set c : ℝ≥0∞ := ∏ j ∈ Finset.range n,
      ENNReal.ofReal (Q (ws j).1 (ws j).2 (ws (j + 1)).1 (ws (j + 1)).2) with hc
    have hsec : ∀ ω, ν (Prod.mk ω ⁻¹' {p : Ω × E | ∀ j ≤ n, W Y z₀ π j p = ws j})
        = Set.indicator {ω | ∀ j ≤ n, Y j ω = (ws j).1} (fun _ => c) ω := by
      intro ω
      by_cases hω : ∀ j ≤ n, Y j ω = (ws j).1
      · rw [Set.indicator_apply, if_pos (show ω ∈ {ω | ∀ j ≤ n, Y j ω = (ws j).1} from hω)]
        have hset : Prod.mk ω ⁻¹' {p : Ω × E | ∀ j ≤ n, W Y z₀ π j p = ws j}
            = π ⁻¹' {g | ∀ j ≤ n, Zmap z₀ (fun k => Y k ω) g j = (ws j).2} := by
          ext e
          simp only [Set.mem_preimage, Set.mem_setOf_eq, W, Prod.ext_iff]
          constructor
          · intro h j hj; exact (h j hj).2
          · intro h j hj; exact ⟨hω j hj, h j hj⟩
        rw [hset, Zmap_set z₀ _ n (fun j => (ws j).2) h0,
          hν n (fun j => (Y j ω, (ws j).2, Y (j + 1) ω)) (fun j => (ws (j + 1)).2), hc]
        apply Finset.prod_congr rfl
        intro j hj
        rw [Finset.mem_range] at hj
        simp only
        rw [hω j (by omega), hω (j + 1) (by omega)]
      · rw [Set.indicator_apply, if_neg (show ω ∉ {ω | ∀ j ≤ n, Y j ω = (ws j).1} from hω)]
        have hset : Prod.mk ω ⁻¹' {p : Ω × E | ∀ j ≤ n, W Y z₀ π j p = ws j} = ∅ := by
          ext e
          simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          intro h
          exact hω (fun j hj => congrArg Prod.fst (h j hj))
        rw [hset, measure_empty]
    rw [lintegral_congr hsec, lintegral_indicator_const hB, hcyl n (fun j => (ws j).1), hc,
      ← ENNReal.ofReal_prod_of_nonneg (fun j _ => hQ _ _ _ _)]
    have hn1 : 0 ≤ ∏ j ∈ Finset.range n, Q (ws j).1 (ws j).2 (ws (j + 1)).1 (ws (j + 1)).2 :=
      Finset.prod_nonneg (fun j _ => hQ _ _ _ _)
    rw [← ENNReal.ofReal_mul hn1]
    congr 1
    unfold K2
    rw [Finset.prod_mul_distrib]
    by_cases hy : (ws 0).1 = y₀
    · rw [if_pos hy, if_pos (Prod.ext hy h0)]; ring
    · rw [if_neg hy, if_neg (fun h => hy (congrArg Prod.fst h))]; ring
  · have hsec : ∀ ω, ν (Prod.mk ω ⁻¹' {p : Ω × E | ∀ j ≤ n, W Y z₀ π j p = ws j}) = 0 := by
      intro ω
      have hset : Prod.mk ω ⁻¹' {p : Ω × E | ∀ j ≤ n, W Y z₀ π j p = ws j} = ∅ := by
        ext e
        simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro h
        have := (h 0 (Nat.zero_le _))
        simp only [W, Prod.ext_iff, Zmap] at this
        exact h0 this.2.symm
      rw [hset, measure_empty]
    rw [lintegral_congr hsec, lintegral_zero, if_neg (fun h => h0 (congrArg Prod.snd h)),
      zero_mul, ENNReal.ofReal_zero]

/-- One-step law of the pair for an increment of a function `f` of the pair. -/
theorem pair_drift {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] (P : Measure Ω)
    (ν : Measure E) [SFinite ν]
    (Ka : S → S → ℝ) (hKa : ∀ a b, 0 ≤ Ka a b)
    (Q : S → S → S → S → ℝ) (hQ : ∀ x z x' z', 0 ≤ Q x z x' z')
    (y₀ z₀ : S) (Y : ℕ → Ω → S) (hY : ∀ n, Measurable (Y n))
    (hcyl : ∀ (n : ℕ) (zs : ℕ → S), P {ω | ∀ j ≤ n, Y j ω = zs j} =
      ENNReal.ofReal ((if zs 0 = y₀ then 1 else 0) * ∏ j ∈ Finset.range n, Ka (zs j) (zs (j + 1))))
    (π : E → ℕ → S × S × S → S) (hπ : Measurable π)
    (hν : ∀ (n : ℕ) (r : ℕ → S × S × S) (zz : ℕ → S),
      ν (π ⁻¹' {g | ∀ j < n, g j (r j) = zz j})
        = ∏ j ∈ Finset.range n, ENNReal.ofReal (Q (r j).1 (r j).2.1 (r j).2.2 (zz j)))
    (f : S × S → ℝ) (n : ℕ) :
    ∫⁻ p, ENNReal.ofReal (f (W Y z₀ π (n + 1) p) - f (W Y z₀ π n p)) ∂(P.prod ν)
      = ∫⁻ p, ∑' b, ENNReal.ofReal (K2 Ka Q (W Y z₀ π n p) b) *
          ENNReal.ofReal (f b - f (W Y z₀ π n p)) ∂(P.prod ν) := by
  have hK2 : ∀ a b : S × S, 0 ≤ K2 Ka Q a b := fun a b => mul_nonneg (hKa _ _) (hQ _ _ _ _)
  exact markov_int (P.prod ν) (K2 Ka Q) hK2 (y₀, z₀) (fun j p => W Y z₀ π j p)
    (fun j => measurable_W Y hY z₀ π hπ j)
    (fun m ws => pair_cyl P ν Ka hKa Q hQ y₀ z₀ Y hY hcyl π hπ hν m ws) n
    (fun xs b => ENNReal.ofReal (f b - f (xs (Fin.last n))))

end Pair

section Gronwall

lemma pos_tele (a : ℕ → ℝ) (n : ℕ) :
    ENNReal.ofReal (a n) ≤ ENNReal.ofReal (a 0) +
      ∑ j ∈ Finset.range n, ENNReal.ofReal (a (j + 1) - a j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← add_assoc]
    calc ENNReal.ofReal (a (n + 1)) = ENNReal.ofReal (a n + (a (n + 1) - a n)) := by ring_nf
      _ ≤ ENNReal.ofReal (a n) + ENNReal.ofReal (a (n + 1) - a n) := ENNReal.ofReal_add_le
      _ ≤ _ := add_le_add ih le_rfl

/-- Gronwall for the accumulated positive increments. -/
theorem gronwall {Ω' : Type*} [MeasurableSpace Ω'] (μ : Measure Ω') (f : ℕ → Ω' → ℝ)
    (hf : ∀ n, Measurable (f n)) (β γ : ℝ≥0∞)
    (h0 : ∫⁻ p, ENNReal.ofReal (f 0 p) ∂μ = 0)
    (hstep : ∀ n, ∫⁻ p, ENNReal.ofReal (f (n + 1) p - f n p) ∂μ
      ≤ β + γ * ∫⁻ p, ENNReal.ofReal (f n p) ∂μ) (n : ℕ) :
    ∫⁻ p, ∑ j ∈ Finset.range n, ENNReal.ofReal (f (j + 1) p - f j p) ∂μ
      ≤ n * β * (1 + γ) ^ n := by
  have hinc : ∀ j, Measurable (fun p => ENNReal.ofReal (f (j + 1) p - f j p)) :=
    fun j => ((hf (j + 1)).sub (hf j)).ennreal_ofReal
  have hsum : ∀ m, ∫⁻ p, ∑ j ∈ Finset.range m, ENNReal.ofReal (f (j + 1) p - f j p) ∂μ
      = ∑ j ∈ Finset.range m, ∫⁻ p, ENNReal.ofReal (f (j + 1) p - f j p) ∂μ :=
    fun m => lintegral_finsetSum _ (fun j _ => hinc j)
  have hF : ∀ m, ∫⁻ p, ENNReal.ofReal (f m p) ∂μ
      ≤ ∑ j ∈ Finset.range m, ∫⁻ p, ENNReal.ofReal (f (j + 1) p - f j p) ∂μ := by
    intro m
    calc ∫⁻ p, ENNReal.ofReal (f m p) ∂μ
        ≤ ∫⁻ p, ENNReal.ofReal (f 0 p) +
            ∑ j ∈ Finset.range m, ENNReal.ofReal (f (j + 1) p - f j p) ∂μ :=
          lintegral_mono (fun p => pos_tele (fun k => f k p) m)
      _ = _ := by rw [lintegral_add_left (hf 0).ennreal_ofReal, h0, zero_add, hsum]
  rw [hsum]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h1 : 1 ≤ (1 + γ) ^ (n + 1) := one_le_pow₀ le_self_add
    calc ∑ j ∈ Finset.range n, ∫⁻ p, ENNReal.ofReal (f (j + 1) p - f j p) ∂μ
          + ∫⁻ p, ENNReal.ofReal (f (n + 1) p - f n p) ∂μ
        ≤ n * β * (1 + γ) ^ n + (β + γ * (n * β * (1 + γ) ^ n)) :=
          add_le_add ih ((hstep n).trans (add_le_add le_rfl (by gcongr; exact (hF n).trans ih)))
      _ = n * β * (1 + γ) ^ (n + 1) + β := by ring
      _ ≤ n * β * (1 + γ) ^ (n + 1) + β * (1 + γ) ^ (n + 1) :=
          add_le_add le_rfl (le_mul_of_one_le_right' h1)
      _ = ((n + 1 : ℕ) : ℝ≥0∞) * β * (1 + γ) ^ (n + 1) := by push_cast; ring

end Gronwall

end SC77K3EP

/-! K3 (d) part 1: the one-step drift is affine in `Dist` with a vanishing constant term. -/

namespace SC77K3F

open StrictCompatLB.MeanField SC77K3D2 SC77K3EA SC77K3EB

lemma inv_deg_pt (d : ℝ) (hd : 0 ≤ d) (K c : ℕ) (hK : 1 ≤ K) :
    d / (c : ℝ) ≤ (if c ≤ K then d else 0) + d / (K : ℝ) := by
  have hKp : (0 : ℝ) < K := by exact_mod_cast hK
  by_cases hc : c ≤ K
  · rw [if_pos hc]
    rcases Nat.eq_zero_or_pos c with h0 | hpos
    · subst h0; simp only [Nat.cast_zero, div_zero]; positivity
    · have h1 : (1 : ℝ) ≤ c := by exact_mod_cast hpos
      exact (div_le_self hd h1).trans (le_add_of_nonneg_right (by positivity))
  · rw [if_neg hc, zero_add]
    have : (K : ℝ) ≤ c := by exact_mod_cast (le_of_lt (not_le.mp hc))
    exact div_le_div_of_nonneg_left hd hKp this

theorem sum_inv_deg (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N)))
    (hsparse : IsPropSparse M G) (d : ℝ) (hd : 0 ≤ d) (K : ℕ) (hK : 1 ≤ K) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∑ w : Fin (M N), d / ((nbrW M G N w).card : ℝ) ≤ (M N : ℝ) * (d * (δ + 1 / K)) := by
  obtain ⟨N₀, hN₀⟩ := SC77K3.small_deg M G hsparse K hK δ hδ
  refine ⟨N₀, fun N hN => ?_⟩
  have hB := hN₀ N hN
  calc ∑ w : Fin (M N), d / ((nbrW M G N w).card : ℝ)
      ≤ ∑ w : Fin (M N), ((if (nbrW M G N w).card ≤ K then d else 0) + d / (K : ℝ)) :=
        Finset.sum_le_sum (fun w _ => inv_deg_pt d hd K _ hK)
    _ = ((Finset.univ.filter (fun w : Fin (M N) => (nbrW M G N w).card ≤ K)).card : ℝ) * d
          + (M N : ℝ) * (d / K) := by
        rw [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero,
          Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, Finset.card_univ,
          Fintype.card_fin]
    _ ≤ δ * (M N : ℝ) * d + (M N : ℝ) * (d / K) := by gcongr
    _ = (M N : ℝ) * (d * (δ + 1 / K)) := by ring

theorem drift_lin (lam : ℝ) (hlam : 0 ≤ lam) (d : ℕ) (hd : 1 ≤ d) (M : ℕ → ℕ)
    (hM : ∀ N, 0 < M N) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (hsparse : IsPropSparse M G)
    (K : ℕ) (hK : 1 ≤ K) (δ : ℝ) (hδ : 0 < δ) (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (∀ w x v, 0 ≤ jsqdRoute M G N d w x v) →
      (∀ w x v, 0 ≤ piRoute M G N (jsqdAssign d) w x v) →
      (∀ w x z, ∑ v, jsqdRoute M G N d w x v = ∑ v, piRoute M G N (jsqdAssign d) w z v) →
      ∀ x z : Fin N → ℕ,
      ∑' p', ENNReal.ofReal (Kc lam M N (jsqdRoute M G N d) (piRoute M G N (jsqdAssign d))
          (x, z) p') * ENNReal.ofReal (Dist p'.1 p'.2 - Dist x z)
        ≤ ENNReal.ofReal (2 * (2 * (d : ℝ) ^ 3 * (δ + 1 / K) + (2 * (d : ℝ) ^ 2 + 2 * d) * η)
            + 2 * (2 * (d : ℝ) ^ 2 + 2 * d) / N * Dist x z) := by
  obtain ⟨N₁, hN₁⟩ := sum_inv_deg M G hsparse (2 * (d : ℝ) ^ 3) (by positivity) K hK δ hδ
  obtain ⟨N₂, hN₂⟩ := SC77K3.avg_frac M G hsparse η hη
  refine ⟨max N₁ N₂, fun N hN hra hrb hs x z => ?_⟩
  refine (drift_jsqd lam hlam d hd M G N hra hrb hs x z).trans (ENNReal.ofReal_le_ofReal ?_)
  set U := Finset.univ.filter (fun v => x v ≠ z v) with hU
  set c : ℝ := 2 * (d : ℝ) ^ 2 + 2 * d with hc
  have hc0 : 0 ≤ c := by positivity
  have hMp : (0 : ℝ) < M N := by exact_mod_cast hM N
  have h1 := hN₁ N (le_of_max_le_left hN)
  have h2 := hN₂ N (le_of_max_le_right hN) U
  have hUD : (U.card : ℝ) / N ≤ Dist x z / N :=
    div_le_div_of_nonneg_right (card_diff_le x z) (Nat.cast_nonneg _)
  set X := ∑ w : Fin (M N), 2 * (2 * (d : ℝ) ^ 3 / (nbrW M G N w).card
            + c * (((nbrW M G N w ∩ U).card : ℝ) / (nbrW M G N w).card)) with hX
  have hXs : X = 2 * ∑ w : Fin (M N), 2 * (d : ℝ) ^ 3 / (nbrW M G N w).card
      + 2 * c * ∑ w : Fin (M N), ((nbrW M G N w ∩ U).card : ℝ) / (nbrW M G N w).card := by
    rw [hX, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun w _ => by ring)
  have hX0 : 0 ≤ X := Finset.sum_nonneg (fun w _ => by positivity)
  have hXle : X ≤ (M N : ℝ) * (2 * (2 * (d : ℝ) ^ 3 * (δ + 1 / K)) + 2 * c * (Dist x z / N + η)) := by
    rw [hXs]
    have := mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left
      (add_le_add hUD le_rfl) hMp.le)) (by positivity : (0 : ℝ) ≤ 2 * c)
    nlinarith
  have hl : lam / (lam + 1) ≤ 1 := div_le_one_of_le₀ (by linarith) (by linarith)
  have hl0 : 0 ≤ lam / (lam + 1) := by positivity
  calc lam / (lam + 1) * (1 / (M N : ℝ)) * X ≤ 1 * (1 / (M N : ℝ)) * X :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hl (by positivity)) hX0
    _ ≤ 1 * (1 / (M N : ℝ)) * ((M N : ℝ) * (2 * (2 * (d : ℝ) ^ 3 * (δ + 1 / K))
          + 2 * c * (Dist x z / N + η))) := mul_le_mul_of_nonneg_left hXle (by positivity)
    _ = 2 * (2 * (d : ℝ) ^ 3 * (δ + 1 / K)) + 2 * c * (Dist x z / N + η) := by
        rw [one_mul, ← mul_assoc, one_div_mul_cancel hMp.ne', one_mul]
    _ = 2 * (2 * (d : ℝ) ^ 3 * (δ + 1 / K) + c * η) + 2 * c / N * Dist x z := by ring

end SC77K3F

/-! K3 (d) part 2: with probability close to one the coupled chains stay `D`-close for `m` steps. -/

namespace SC77K3G

open StrictCompatLB.MeanField SC77K3D SC77K3D3 SC77K3D4 SC77K3D2 SC77K3EA

variable (lam : ℝ) (d : ℕ) (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N)))

theorem far_prob (hlam : 0 ≤ lam) (hd : 1 ≤ d) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (z₀ : (N : ℕ) → Fin N → ℕ) (Y : (N : ℕ) → ℕ → Ω → (Fin N → ℕ)) (τ : ℕ → ℕ → Ω → ℝ) (N : ℕ)
    (hY : IsLBProcess P lam M N (jsqdRoute M G N d) (z₀ N) (Y N) (τ N))
    (β γ : ℝ) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (hdrift : ∀ x z : Fin N → ℕ,
      ∑' p', ENNReal.ofReal (Kc lam M N (jsqdRoute M G N d) (piRoute M G N (jsqdAssign d))
          (x, z) p') * ENNReal.ofReal (Dist p'.1 p'.2 - Dist x z)
        ≤ ENNReal.ofReal (β + γ * Dist x z))
    (m : ℕ) (D : ℝ) (hD : 0 < D) :
    (P.prod (nu lam d M G hlam hd)) {p | ¬ ∀ n ≤ m, Dist (Y N n p.1) (Zc z₀ Y N n p) ≤ D}
      ≤ (m * ENNReal.ofReal β * (1 + ENNReal.ofReal γ) ^ m) / ENNReal.ofReal D := by
  obtain ⟨hP, hYm, hcyl, -, -, -, -⟩ := hY
  haveI := hP
  haveI := nu_prob lam d M G hlam hd
  set ν := nu lam d M G hlam hd with hν
  have hWm : ∀ n, Measurable (SC77K3EP.W (Y N) (z₀ N) (fun e : EE => e N) n) :=
    fun n => SC77K3EP.measurable_W (Y N) hYm (z₀ N) _ (measurable_pi_apply N) n
  set f : ℕ → Ω × EE → ℝ := fun n p => Dist (SC77K3EP.W (Y N) (z₀ N) (fun e : EE => e N) n p).1
    (SC77K3EP.W (Y N) (z₀ N) (fun e : EE => e N) n p).2 with hf
  have hfm : ∀ n, Measurable (f n) := fun n =>
    (measurable_of_countable (fun a : (Fin N → ℕ) × (Fin N → ℕ) => Dist a.1 a.2)).comp (hWm n)
  have hra := jr_nonneg d M G N
  have hrb := pr_nonneg d M G N
  have hs := hs_eq d M G hd N
  have hK2 : ∀ a b, SC77K3EP.K2 (lbKernel lam M N (jsqdRoute M G N d)) (QN lam d M G N) a b
      = Kc lam M N (jsqdRoute M G N d) (piRoute M G N (jsqdAssign d)) a b := by
    intro a b
    obtain ⟨x, z⟩ := a
    obtain ⟨x', z'⟩ := b
    exact K_mul_Q lam M N _ _ hlam hra hrb hs x z x' z'
  have hstep : ∀ n, ∫⁻ p, ENNReal.ofReal (f (n + 1) p - f n p) ∂(P.prod ν)
      ≤ ENNReal.ofReal β + ENNReal.ofReal γ * ∫⁻ p, ENNReal.ofReal (f n p) ∂(P.prod ν) := by
    intro n
    refine (le_of_eq (SC77K3EP.pair_drift P ν (lbKernel lam M N (jsqdRoute M G N d))
      (lbK_nonneg lam M hlam N _ hra) (QN lam d M G N)
      (fun x z x' z' => Q_nonneg lam M N _ _ hlam hra hrb x z x' z')
      (z₀ N) (z₀ N) (Y N) hYm hcyl (fun e : EE => e N) (measurable_pi_apply N)
      (fun n r zz => nu_cyl lam d M G hlam hd N n r zz) (fun b => Dist b.1 b.2) n)).trans ?_
    calc ∫⁻ p, ∑' b, ENNReal.ofReal (SC77K3EP.K2 (lbKernel lam M N (jsqdRoute M G N d))
            (QN lam d M G N) (SC77K3EP.W (Y N) (z₀ N) (fun e : EE => e N) n p) b) *
          ENNReal.ofReal (Dist b.1 b.2 - Dist (SC77K3EP.W (Y N) (z₀ N) (fun e : EE => e N) n p).1
            (SC77K3EP.W (Y N) (z₀ N) (fun e : EE => e N) n p).2) ∂(P.prod ν)
        ≤ ∫⁻ p, ENNReal.ofReal (β + γ * f n p) ∂(P.prod ν) := by
          apply lintegral_mono
          intro p
          dsimp only
          rw [tsum_congr (fun b => by rw [hK2])]
          exact hdrift _ _
      _ = ENNReal.ofReal β + ENNReal.ofReal γ * ∫⁻ p, ENNReal.ofReal (f n p) ∂(P.prod ν) := by
          rw [lintegral_congr (fun p => ENNReal.ofReal_add hβ (mul_nonneg hγ (Dist_nonneg _ _))),
            lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_congr (fun p => ENNReal.ofReal_mul hγ),
            lintegral_const_mul _ (hfm n).ennreal_ofReal]
  have hY0 : P {ω | Y N 0 ω ≠ z₀ N} = 0 := by
    have h1 := hcyl 0 (fun _ => z₀ N)
    rw [if_pos rfl, Finset.range_zero, Finset.prod_empty, mul_one, ENNReal.ofReal_one] at h1
    have hset : {ω | ∀ j ≤ 0, Y N j ω = z₀ N} = {ω | Y N 0 ω = z₀ N} := by
      ext ω
      simp only [Set.mem_setOf_eq, Nat.le_zero, forall_eq]
    rw [hset] at h1
    have hm : MeasurableSet {ω | Y N 0 ω = z₀ N} := (measurableSet_singleton _).preimage (hYm 0)
    exact (prob_compl_eq_zero_iff hm).mpr h1
  have hnull : (P.prod ν) {p | f 0 p ≠ 0} = 0 := by
    apply measure_mono_null (t := Prod.fst ⁻¹' {ω | Y N 0 ω ≠ z₀ N})
    · intro p hp
      simp only [Set.mem_preimage, Set.mem_setOf_eq] at hp ⊢
      intro heq
      apply hp
      show Dist (Y N 0 p.1) (z₀ N) = 0
      rw [heq]
      exact Dist_self _
    · rw [← Set.prod_univ, Measure.prod_prod, hY0, zero_mul]
  have h0 : ∫⁻ p, ENNReal.ofReal (f 0 p) ∂(P.prod ν) = 0 := by
    rw [lintegral_eq_zero_iff (hfm 0).ennreal_ofReal]
    have hae : ∀ᵐ p ∂(P.prod ν), f 0 p = 0 := ae_iff.mpr hnull
    filter_upwards [hae] with p hp
    rw [hp]
    simp
  have hC := SC77K3EP.gronwall (P.prod ν) f hfm (ENNReal.ofReal β) (ENNReal.ofReal γ) h0 hstep m
  have hCm : Measurable (fun p => ∑ j ∈ Finset.range m, ENNReal.ofReal (f (j + 1) p - f j p)) :=
    Finset.measurable_sum _ (fun j _ => ((hfm (j + 1)).sub (hfm j)).ennreal_ofReal)
  have hsub : {p : Ω × EE | ¬ ∀ n ≤ m, Dist (Y N n p.1) (Zc z₀ Y N n p) ≤ D}
      ⊆ {p | f 0 p ≠ 0} ∪
        {p | ENNReal.ofReal D ≤ ∑ j ∈ Finset.range m, ENNReal.ofReal (f (j + 1) p - f j p)} := by
    intro p hp
    simp only [Set.mem_setOf_eq, not_forall, not_le] at hp
    obtain ⟨n, hn, hDn⟩ := hp
    by_cases h0p : f 0 p = 0
    · right
      have ht := SC77K3EP.pos_tele (fun k => f k p) n
      rw [h0p, ENNReal.ofReal_zero, zero_add] at ht
      have hmono : ∑ j ∈ Finset.range n, ENNReal.ofReal (f (j + 1) p - f j p)
          ≤ ∑ j ∈ Finset.range m, ENNReal.ofReal (f (j + 1) p - f j p) :=
        Finset.sum_le_sum_of_subset (Finset.range_mono hn)
      exact (ENNReal.ofReal_le_ofReal hDn.le).trans (ht.trans hmono)
    · left
      exact h0p
  calc (P.prod ν) {p | ¬ ∀ n ≤ m, Dist (Y N n p.1) (Zc z₀ Y N n p) ≤ D}
      ≤ (P.prod ν) {p | f 0 p ≠ 0} + (P.prod ν)
          {p | ENNReal.ofReal D ≤ ∑ j ∈ Finset.range m, ENNReal.ofReal (f (j + 1) p - f j p)} :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ (∫⁻ p, ∑ j ∈ Finset.range m, ENNReal.ofReal (f (j + 1) p - f j p) ∂(P.prod ν))
          / ENNReal.ofReal D := by
        rw [hnull, zero_add]
        exact meas_ge_le_lintegral_div hCm.aemeasurable (ENNReal.ofReal_pos.mpr hD).ne'
          ENNReal.ofReal_ne_top
    _ ≤ _ := by gcongr

end SC77K3G

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SC77K3E

open StrictCompatLB.MeanField

/-! K3e step count: with i.i.d. Exp(r) gaps, the number of clock epochs by time `T` exceeds `m`
with probability at most `e^{rT} 2^{-(m+1)}` (Chernoff with `t = -r`). -/

lemma expM_Iio (r : ℝ) (hr : 0 < r) : expMeasure r (Set.Iio 0) = 0 := by
  haveI := isProbabilityMeasure_expMeasure hr
  have h := cdf_expMeasure_eq hr 0
  rw [if_pos le_rfl, mul_zero, neg_zero, Real.exp_zero, sub_self, cdf_eq_real,
    measureReal_def] at h
  have h0 : expMeasure r (Set.Iic 0) = 0 :=
    ((ENNReal.toReal_eq_zero_iff _).mp h).resolve_right (measure_ne_top _ _)
  exact measure_mono_null Set.Iio_subset_Iic_self h0

lemma lint_exp (r : ℝ) (hr : 0 < r) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (-r * x)) ∂(expMeasure r) = ENNReal.ofReal (1 / 2) := by
  have h1 : expMeasure r = volume.withDensity (exponentialPDF r) := rfl
  have hm : Measurable (exponentialPDF r) := (measurable_exponentialPDFReal r).ennreal_ofReal
  have hg : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (-r * x))) := by fun_prop
  rw [h1, lintegral_withDensity_eq_lintegral_mul _ hm hg]
  have hpt : ∀ x, (exponentialPDF r * fun x => ENNReal.ofReal (Real.exp (-r * x))) x
      = ENNReal.ofReal (1 / 2) * exponentialPDF (2 * r) x := by
    intro x
    simp only [Pi.mul_apply, Function.comp_apply]
    by_cases hx : 0 ≤ x
    · rw [exponentialPDF_of_nonneg hx, exponentialPDF_of_nonneg hx,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      rw [mul_assoc, ← Real.exp_add]
      have : -(r * x) + -r * x = -(2 * r * x) := by ring
      rw [this]
      ring
    · rw [exponentialPDF_of_neg (lt_of_not_ge hx), exponentialPDF_of_neg (lt_of_not_ge hx),
        zero_mul, mul_zero]
  have hm2 : Measurable (exponentialPDF (2 * r)) := (measurable_exponentialPDFReal _).ennreal_ofReal
  rw [lintegral_congr hpt, lintegral_const_mul _ hm2,
    lintegral_exponentialPDF_eq_one (by linarith), mul_one]

lemma int_exp (r : ℝ) (hr : 0 < r) : ∫ x, Real.exp (-r * x) ∂(expMeasure r) = 1 / 2 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun x => (Real.exp_pos _).le))
    (by fun_prop : Measurable (fun x : ℝ => Real.exp (-r * x))).aestronglyMeasurable,
    lint_exp r hr, ENNReal.toReal_ofReal (by norm_num)]

variable (r : ℝ) (hr : 0 < r) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
  (τ : ℕ → Ω → ℝ) (hτ : ∀ k, Measurable (τ k)) (hlaw : ∀ k, P.map (τ k) = expMeasure r)

include hr hτ hlaw in
lemma tau_nonneg : ∀ᵐ ω ∂P, ∀ k, 0 ≤ τ k ω := by
  rw [ae_all_iff]
  intro k
  have h : P (τ k ⁻¹' Set.Iio 0) = 0 := by
    rw [← Measure.map_apply (hτ k) measurableSet_Iio, hlaw k, expM_Iio r hr]
  refine ae_iff.mpr ?_
  convert h using 2
  ext ω
  simp

include hr hτ hlaw in
lemma mgf_tau (k : ℕ) : mgf (τ k) P (-r) = 1 / 2 := by
  have hsm : AEStronglyMeasurable (fun x => Real.exp (-r * x)) (P.map (τ k)) :=
    (by fun_prop : Measurable (fun x : ℝ => Real.exp (-r * x))).aestronglyMeasurable
  calc mgf (τ k) P (-r) = ∫ x, Real.exp (-r * x) ∂(P.map (τ k)) :=
        (integral_map (hτ k).aemeasurable hsm).symm
    _ = 1 / 2 := by rw [hlaw k, int_exp r hr]

include hr hτ hlaw in
theorem steps [IsProbabilityMeasure P] (hind : iIndepFun τ P) (m : ℕ) (T : ℝ) :
    P {ω | m < epochCount (fun k => τ k ω) T}
      ≤ ENNReal.ofReal (Real.exp (r * T) * (1 / 2) ^ (m + 1)) := by
  have hsub : {ω | m < epochCount (fun k => τ k ω) T}
      ⊆ {ω | (∑ k ∈ Finset.range (m + 1), τ k) ω ≤ T} ∪ {ω | ¬ ∀ k, 0 ≤ τ k ω} := by
    intro ω hω
    by_cases hnn : ∀ k, 0 ≤ τ k ω
    · left
      simp only [Set.mem_setOf_eq, Finset.sum_apply] at hω ⊢
      unfold epochCount at hω
      have hne : {n : ℕ | ∑ k ∈ Finset.range n, τ k ω ≤ T}.Nonempty := by
        by_contra h
        rw [Set.not_nonempty_iff_eq_empty] at h
        rw [h] at hω
        simp at hω
      obtain ⟨n, hn, hmn⟩ := exists_lt_of_lt_csSup hne hω
      calc ∑ k ∈ Finset.range (m + 1), τ k ω ≤ ∑ k ∈ Finset.range n, τ k ω :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
              (fun k _ _ => hnn k)
        _ ≤ T := hn
    · right
      exact hnn
  have hnull : P {ω | ¬ ∀ k, 0 ≤ τ k ω} = 0 := ae_iff.mp (tau_nonneg r hr P τ hτ hlaw)
  have hSm : Measurable (∑ k ∈ Finset.range (m + 1), τ k) := by
    rw [Finset.sum_fn]
    exact Finset.measurable_sum _ (fun k _ => hτ k)
  have hint : Integrable (fun ω => Real.exp (-r * (∑ k ∈ Finset.range (m + 1), τ k) ω)) P := by
    refine Integrable.mono' (integrable_const (1 : ℝ))
      (Real.measurable_exp.comp (hSm.const_mul (-r))).aestronglyMeasurable ?_
    filter_upwards [tau_nonneg r hr P τ hτ hlaw] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    have hS : 0 ≤ (∑ k ∈ Finset.range (m + 1), τ k) ω := by
      rw [Finset.sum_apply]
      exact Finset.sum_nonneg fun k _ => hω k
    nlinarith
  have hch := measure_le_le_exp_mul_mgf (μ := P) (X := ∑ k ∈ Finset.range (m + 1), τ k) T
    (by linarith : -r ≤ 0) hint
  rw [hind.mgf_sum hτ, Finset.prod_congr rfl (fun k _ => mgf_tau r hr P τ hτ hlaw k),
    Finset.prod_const, Finset.card_range, neg_neg] at hch
  have hS : P {ω | (∑ k ∈ Finset.range (m + 1), τ k) ω ≤ T}
      ≤ ENNReal.ofReal (Real.exp (r * T) * (1 / 2) ^ (m + 1)) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
    exact ENNReal.ofReal_le_ofReal (by rw [← measureReal_def]; exact hch)
  calc P {ω | m < epochCount (fun k => τ k ω) T}
      ≤ P ({ω | (∑ k ∈ Finset.range (m + 1), τ k) ω ≤ T} ∪ {ω | ¬ ∀ k, 0 ≤ τ k ω}) :=
        measure_mono hsub
    _ ≤ P {ω | (∑ k ∈ Finset.range (m + 1), τ k) ω ≤ T} + P {ω | ¬ ∀ k, 0 ≤ τ k ω} :=
        measure_union_le _ _
    _ ≤ _ := by rw [hnull, add_zero]; exact hS

end SC77K3E

/-! K3e (c): occupancy distance and the sup comparison along a shared clock (session 11). -/

namespace SC77K3EC

open StrictCompatLB.MeanField SC77K3EA PowerOfDUniversality.Fluid

lemma ind_term (a b : ℕ) (hab : a ≤ b) (i : ℕ) :
    ENNReal.ofReal |(if i ≤ a then (1 : ℝ) else 0) - (if i ≤ b then 1 else 0)|
      = if i ∈ Finset.Ioc a b then 1 else 0 := by
  simp only [Finset.mem_Ioc]
  by_cases h1 : i ≤ a
  · have h2 : i ≤ b := le_trans h1 hab
    simp [h1, h2, not_lt.mpr h1]
  · by_cases h2 : i ≤ b
    · have h3 : a < i := lt_of_not_ge h1
      simp [h1, h2, h3]
    · simp [h1, h2]

lemma ind_tsum_le (a b : ℕ) (hab : a ≤ b) :
    ∑' i : ℕ, ENNReal.ofReal |(if i ≤ a then (1 : ℝ) else 0) - (if i ≤ b then 1 else 0)|
      = ENNReal.ofReal |(a : ℝ) - (b : ℝ)| := by
  simp only [ind_term a b hab]
  rw [tsum_eq_sum (s := Finset.Ioc a b) (fun i hi => if_neg hi),
    Finset.sum_congr rfl (fun i hi => if_pos hi), Finset.sum_const, nsmul_one, Nat.card_Ioc]
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  rw [abs_sub_comm, abs_of_nonneg (by linarith),
    show (b : ℝ) - a = ((b - a : ℕ) : ℝ) by rw [Nat.cast_sub hab], ENNReal.ofReal_natCast]

lemma ind_tsum (a b : ℕ) :
    ∑' i : ℕ, ENNReal.ofReal |(if i ≤ a then (1 : ℝ) else 0) - (if i ≤ b then 1 else 0)|
      = ENNReal.ofReal |(a : ℝ) - (b : ℝ)| := by
  rcases le_total a b with h | h
  · exact ind_tsum_le a b h
  · simp_rw [abs_sub_comm (if _ ≤ a then (1 : ℝ) else 0)]
    rw [ind_tsum_le b a h, abs_sub_comm]

lemma occ_sub {N : ℕ} (x z : Fin N → ℕ) (i : ℕ) :
    occ x i - occ z i
      = (∑ v, ((if i ≤ x v then (1 : ℝ) else 0) - (if i ≤ z v then 1 else 0))) / N := by
  unfold occ Qcount
  rw [Finset.card_filter, Finset.card_filter]
  push_cast
  rw [← sub_div, ← Finset.sum_sub_distrib]

theorem l1dist_occ_le {N : ℕ} (x z : Fin N → ℕ) :
    l1dist (occ x) (occ z) ≤ ENNReal.ofReal (Dist x z / N) := by
  unfold l1dist
  have hN : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
  have hpt : ∀ i : ℕ, ENNReal.ofReal |occ x i - occ z i|
      ≤ ENNReal.ofReal (1 / (N : ℝ)) * ∑ v, ENNReal.ofReal
          |(if i ≤ x v then (1 : ℝ) else 0) - (if i ≤ z v then 1 else 0)| := by
    intro i
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _), ← ENNReal.ofReal_mul hN]
    apply ENNReal.ofReal_le_ofReal
    rw [occ_sub, abs_div, Nat.abs_cast, one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)
  calc ∑' i, ENNReal.ofReal |occ x i - occ z i|
      ≤ ∑' i, ENNReal.ofReal (1 / (N : ℝ)) * ∑ v, ENNReal.ofReal
          |(if i ≤ x v then (1 : ℝ) else 0) - (if i ≤ z v then 1 else 0)| :=
        ENNReal.tsum_le_tsum hpt
    _ = ENNReal.ofReal (1 / (N : ℝ)) * ∑ v, ∑' i : ℕ, ENNReal.ofReal
          |(if i ≤ x v then (1 : ℝ) else 0) - (if i ≤ z v then 1 else 0)| := by
        rw [ENNReal.tsum_mul_left, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    _ = ENNReal.ofReal (1 / (N : ℝ)) * ∑ v, ENNReal.ofReal |(x v : ℝ) - (z v : ℝ)| := by
        simp only [ind_tsum]
    _ = ENNReal.ofReal (Dist x z / N) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _), ← ENNReal.ofReal_mul hN]
        unfold SC77K3EA.Dist
        congr 1
        ring

lemma l1_tri (a b c : ℕ → ℝ) : l1dist a c ≤ l1dist a b + l1dist b c := by
  unfold l1dist
  rw [← ENNReal.tsum_add]
  exact ENNReal.tsum_le_tsum fun i =>
    (ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)).trans ENNReal.ofReal_add_le

/-- K3e (c): along a shared clock, the sup-distance of the `Y` occupancy path to `s` exceeds
that of the `Z` path by at most `D/N` when `Dist(Y_n, Z_n) ≤ D` for all epochs used. -/
theorem sup_compare {Ω : Type*} {N : ℕ} (Y Z : ℕ → Ω → (Fin N → ℕ)) (τ : ℕ → Ω → ℝ) (ω : Ω)
    (s : ℝ → ℕ → ℝ) (T : ℝ) (m : ℕ) (D : ℝ)
    (hm : ∀ t ∈ Set.Icc 0 T, epochCount (fun k => τ k ω) t ≤ m)
    (hD : ∀ n ≤ m, Dist (Y n ω) (Z n ω) ≤ D) :
    supDistL1 (occPath Y τ ω) s T ≤ supDistL1 (occPath Z τ ω) s T + ENNReal.ofReal (D / N) := by
  unfold supDistL1
  refine iSup₂_le fun t ht => ?_
  have h1 : occPath Y τ ω t = occ (Y (epochCount (fun k => τ k ω) t) ω) := rfl
  have h2 : occPath Z τ ω t = occ (Z (epochCount (fun k => τ k ω) t) ω) := rfl
  calc l1dist (occPath Y τ ω t) (s t)
      ≤ l1dist (occ (Y (epochCount (fun k => τ k ω) t) ω)) (occ (Z (epochCount (fun k => τ k ω) t) ω))
        + l1dist (occPath Z τ ω t) (s t) := by
        rw [h1, h2]
        exact l1_tri _ _ _
    _ ≤ ENNReal.ofReal (D / N)
        + ⨆ (t : ℝ) (_ : t ∈ Set.Icc 0 T), l1dist (occPath Z τ ω t) (s t) := by
        refine add_le_add ?_ ?_
        · exact (l1dist_occ_le _ _).trans (ENNReal.ofReal_le_ofReal
            (div_le_div_of_nonneg_right (hD _ (hm t ht)) (Nat.cast_nonneg _)))
        · exact le_iSup₂ (f := fun t (_ : t ∈ Set.Icc 0 T) => l1dist (occPath Z τ ω t) (s t)) t ht
    _ = _ := add_comm _ _

/-- On the good event `T < τ 0 + ⋯ + τ m` (nonnegative gaps) no time `t ≤ T` sees more than
`m` epochs. -/
lemma epoch_le (τ : ℕ → ℝ) (hτ : ∀ k, 0 ≤ τ k) (T : ℝ) (m : ℕ)
    (hT : T < ∑ k ∈ Finset.range (m + 1), τ k) (t : ℝ) (ht : t ≤ T) :
    epochCount τ t ≤ m := by
  unfold epochCount
  apply csSup_le'
  intro n hn
  have hn' : ∑ k ∈ Finset.range n, τ k ≤ t := hn
  by_contra h
  have h' : m + 1 ≤ n := Nat.succ_le_of_lt (not_le.mp h)
  have : ∑ k ∈ Finset.range (m + 1), τ k ≤ ∑ k ∈ Finset.range n, τ k :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h') (fun k _ _ => hτ k)
  linarith

end SC77K3EC

/-! K3 (d) part 3: the Chernoff bound on the clock sum, and the assembly of K3. -/

namespace SC77K3E

theorem sum_small (r : ℝ) (hr : 0 < r) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (τ : ℕ → Ω → ℝ) (hτ : ∀ k, Measurable (τ k))
    (hlaw : ∀ k, P.map (τ k) = expMeasure r) (hind : iIndepFun τ P) (m : ℕ) (T : ℝ) :
    P {ω | (∑ k ∈ Finset.range (m + 1), τ k) ω ≤ T}
      ≤ ENNReal.ofReal (Real.exp (r * T) * (1 / 2) ^ (m + 1)) := by
  have hSm : Measurable (∑ k ∈ Finset.range (m + 1), τ k) := by
    rw [Finset.sum_fn]
    exact Finset.measurable_sum _ (fun k _ => hτ k)
  have hint : Integrable (fun ω => Real.exp (-r * (∑ k ∈ Finset.range (m + 1), τ k) ω)) P := by
    refine Integrable.mono' (integrable_const (1 : ℝ))
      (Real.measurable_exp.comp (hSm.const_mul (-r))).aestronglyMeasurable ?_
    filter_upwards [tau_nonneg r hr P τ hτ hlaw] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    have hS : 0 ≤ (∑ k ∈ Finset.range (m + 1), τ k) ω := by
      rw [Finset.sum_apply]
      exact Finset.sum_nonneg fun k _ => hω k
    nlinarith
  have hch := measure_le_le_exp_mul_mgf (μ := P) (X := ∑ k ∈ Finset.range (m + 1), τ k) T
    (by linarith : -r ≤ 0) hint
  rw [hind.mgf_sum hτ, Finset.prod_congr rfl (fun k _ => mgf_tau r hr P τ hτ hlaw k),
    Finset.prod_const, Finset.card_range, neg_neg] at hch
  rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
  exact ENNReal.ofReal_le_ofReal (by rw [← measureReal_def]; exact hch)

end SC77K3E

namespace SC77K3H

open StrictCompatLB.MeanField SC77K3D4 SC77K3EA

set_option maxHeartbeats 1600000 in
theorem k3 : ∀ (lam : ℝ), 0 < lam → lam < 1 → ∀ (d : ℕ), 2 ≤ d →
  ∀ (M : ℕ → ℕ), (∀ N, 0 < M N) → ∀ (G : (N : ℕ) → Finset (Fin N × Fin (M N))),
  IsConnectedSeq M G → IsPropSparse M G →
  ∀ (z₀ : (N : ℕ) → Fin N → ℕ) (s : ℝ → ℕ → ℝ) (T : ℝ), 0 ≤ T →
  (∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (Y : (N : ℕ) → ℕ → Ω → (Fin N → ℕ)) (τ : ℕ → ℕ → Ω → ℝ),
      (∀ N, 1 ≤ N → IsLBProcess P lam M N (piRoute M G N (jsqdAssign d)) (z₀ N) (Y N) (τ N)) →
      ∀ ε : ℝ, 0 < ε → Tendsto (fun N => P {ω | ENNReal.ofReal ε ≤
          PowerOfDUniversality.Fluid.supDistL1 (occPath (Y N) (τ N) ω) s T}) atTop (𝓝 0)) →
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (Y : (N : ℕ) → ℕ → Ω → (Fin N → ℕ)) (τ : ℕ → ℕ → Ω → ℝ),
      (∀ N, 1 ≤ N → IsLBProcess P lam M N (jsqdRoute M G N d) (z₀ N) (Y N) (τ N)) →
      ∀ ε : ℝ, 0 < ε → Tendsto (fun N => P {ω | ENNReal.ofReal ε ≤
          PowerOfDUniversality.Fluid.supDistL1 (occPath (Y N) (τ N) ω) s T}) atTop (𝓝 0) := by
  intro lam hlam0 _hlam1 d hd2 M hM G _hconn hsparse z₀ s T hT Hpi Ω _ P Y τ hY ε hε
  have hlam : 0 ≤ lam := hlam0.le
  have hd : 1 ≤ d := by omega
  have hZ : ∀ N, 1 ≤ N → IsLBProcess (P.prod (nu lam d M G hlam hd)) lam M N
      (piRoute M G N (jsqdAssign d)) (z₀ N) (Zc z₀ Y N) (fun k p => τ N k p.1) :=
    fun N hN => Z_isLB lam d M G hlam hd P z₀ Y τ N (hY N hN)
  have hA := Hpi (Ω × EE) (P.prod (nu lam d M G hlam hd)) (Zc z₀ Y) (fun N k p => τ N k p.1)
    hZ (ε / 2) (by linarith)
  rw [ENNReal.tendsto_nhds_zero] at hA ⊢
  intro e he
  obtain ⟨r0, _, hr0pos, hr0e⟩ := ENNReal.lt_iff_exists_real_btwn.mp he
  have hr0p : 0 < r0 := ENNReal.ofReal_pos.mp hr0pos
  obtain ⟨e₁, he₁⟩ : ∃ e₁ : ℝ, e₁ = r0 / 3 := ⟨_, rfl⟩
  have he₁p : 0 < e₁ := by rw [he₁]; positivity
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = 2 * (lam + 1) * T + 3 := ⟨_, rfl⟩
  have hLp : 0 < L := by rw [hL]; positivity
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 2 * (d : ℝ) ^ 2 + 2 * d := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  obtain ⟨A, hA'⟩ : ∃ A : ℝ, A = 2 * (d : ℝ) ^ 3 := ⟨_, rfl⟩
  have hAp : 0 < A := by rw [hA']; positivity
  obtain ⟨β₀, hβ₀⟩ : ∃ β₀ : ℝ, β₀ = e₁ * ε / (2 * L * Real.exp (2 * c * L)) := ⟨_, rfl⟩
  have hβ₀p : 0 < β₀ := by rw [hβ₀]; positivity
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ⌈6 * A / β₀⌉₊ + 1 := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := by omega
  have hKp : (0 : ℝ) < K := by exact_mod_cast hK1
  have hAK : A * (1 / K) ≤ β₀ / 6 := by
    have hKr : 6 * A / β₀ ≤ (K : ℝ) := by
      rw [hK]; push_cast; linarith [Nat.le_ceil (6 * A / β₀)]
    rw [div_le_iff₀ hβ₀p] at hKr
    rw [mul_one_div, div_le_iff₀ hKp]
    nlinarith
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = β₀ / (6 * A) := ⟨_, rfl⟩
  have hδp : 0 < δ := by rw [hδ]; positivity
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = β₀ / (6 * (c + 1)) := ⟨_, rfl⟩
  have hηp : 0 < η := by rw [hη]; positivity
  have hAδ : A * δ = β₀ / 6 := by rw [hδ]; field_simp
  have hcη : c * η ≤ β₀ / 6 := by
    rw [hη, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hβ : 2 * (A * (δ + 1 / K) + c * η) ≤ β₀ := by
    rw [mul_add A δ, hAδ]; linarith
  obtain ⟨N₀, hN₀⟩ := SC77K3F.drift_lin lam hlam d hd M hM G hsparse K hK1 δ hδp η hηp
  have hB : Tendsto (fun N : ℕ => ((1 : ℝ) / 2) ^ (N + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
      (tendsto_add_atTop_nat 1)
  filter_upwards [hA (ENNReal.ofReal e₁) (ENNReal.ofReal_pos.mpr he₁p),
    hB.eventually (ge_mem_nhds he₁p), eventually_ge_atTop (max N₀ 1)] with N hN1 hN2 hN3
  have hN1' : 1 ≤ N := le_of_max_le_right hN3
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1'
  have hNp : (0 : ℝ) < N := by linarith
  obtain ⟨hP, _, _, hτm, hind, hlaw, -⟩ := hY N hN1'
  haveI := hP
  haveI := nu_prob lam d M G hlam hd
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (lam + 1) * N := ⟨_, rfl⟩
  have hrp : 0 < r := by rw [hr]; positivity
  rw [← hr] at hlaw
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = 2 * ⌈r * T⌉₊ + N := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = ε * N / 2 := ⟨_, rfl⟩
  have hDp : 0 < D := by rw [hD]; positivity
  have hfst : ∀ B : Set Ω, (P.prod (nu lam d M G hlam hd)) (Prod.fst ⁻¹' B) = P B := by
    intro B
    rw [← Set.prod_univ, Measure.prod_prod, measure_univ, mul_one]
  -- clock sum
  have hexp : Real.exp (r * T) * (1 / 2 : ℝ) ^ (m + 1) ≤ (1 / 2 : ℝ) ^ (N + 1) := by
    have h1 : Real.exp (r * T) ≤ (4 : ℝ) ^ ⌈r * T⌉₊ := by
      calc Real.exp (r * T) ≤ Real.exp (⌈r * T⌉₊ : ℝ) := Real.exp_le_exp.mpr (Nat.le_ceil _)
        _ = Real.exp 1 ^ ⌈r * T⌉₊ := by rw [← Real.exp_nat_mul, mul_one]
        _ ≤ (4 : ℝ) ^ ⌈r * T⌉₊ :=
          pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith [Real.exp_one_lt_d9]) _
    have h2 : (1 / 2 : ℝ) ^ (m + 1) = (1 / 4 : ℝ) ^ ⌈r * T⌉₊ * (1 / 2) ^ (N + 1) := by
      rw [show m + 1 = 2 * ⌈r * T⌉₊ + (N + 1) by omega, pow_add, pow_mul]
      norm_num
    have h3 : Real.exp (r * T) * (1 / 4 : ℝ) ^ ⌈r * T⌉₊ ≤ 1 := by
      calc Real.exp (r * T) * (1 / 4 : ℝ) ^ ⌈r * T⌉₊
          ≤ (4 : ℝ) ^ ⌈r * T⌉₊ * (1 / 4) ^ ⌈r * T⌉₊ :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = 1 := by rw [← mul_pow]; norm_num
    rw [h2, ← mul_assoc]
    calc Real.exp (r * T) * (1 / 4 : ℝ) ^ ⌈r * T⌉₊ * (1 / 2) ^ (N + 1)
        ≤ 1 * (1 / 2 : ℝ) ^ (N + 1) := mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = _ := one_mul _
  have hE2 : P {ω | (∑ k ∈ Finset.range (m + 1), τ N k) ω ≤ T} ≤ ENNReal.ofReal e₁ :=
    (SC77K3E.sum_small r hrp P (τ N) hτm hlaw hind m T).trans
      (ENNReal.ofReal_le_ofReal (hexp.trans hN2))
  have hE3 : P {ω | ¬ ∀ k, 0 ≤ τ N k ω} = 0 :=
    ae_iff.mp (SC77K3E.tau_nonneg r hrp P (τ N) hτm hlaw)
  -- coupling term
  have hβnn : 0 ≤ 2 * (A * (δ + 1 / K) + c * η) := by positivity
  have hγnn : 0 ≤ 2 * c / N := by positivity
  have hdr : ∀ x z : Fin N → ℕ,
      ∑' p', ENNReal.ofReal (SC77K3D2.Kc lam M N (jsqdRoute M G N d)
          (piRoute M G N (jsqdAssign d)) (x, z) p') * ENNReal.ofReal (Dist p'.1 p'.2 - Dist x z)
        ≤ ENNReal.ofReal (2 * (A * (δ + 1 / K) + c * η) + 2 * c / N * Dist x z) := by
    intro x z
    have := hN₀ N (le_of_max_le_left hN3) (jr_nonneg d M G N) (pr_nonneg d M G N)
      (hs_eq d M G hd N) x z
    rw [hA', hc]
    convert this using 4
  have hE4 := SC77K3G.far_prob lam d M G hlam hd P z₀ Y τ N (hY N hN1')
    (2 * (A * (δ + 1 / K) + c * η)) (2 * c / N) hβnn hγnn hdr m D hDp
  have hmL : (m : ℝ) ≤ L * N := by
    have h1 : (⌈r * T⌉₊ : ℝ) < r * T + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : (m : ℝ) = 2 * (⌈r * T⌉₊ : ℝ) + N := by rw [hm]; push_cast; ring
    have hrT : r * T = (lam + 1) * T * N := by rw [hr]; ring
    rw [h2, hL]
    nlinarith [hrT, h1, hNr]
  have hpow : (1 + 2 * c / N) ^ m ≤ Real.exp (2 * c * L) := by
    calc (1 + 2 * c / N) ^ m ≤ (Real.exp (2 * c / N)) ^ m :=
          pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (2 * c / N)]) m
      _ = Real.exp (m * (2 * c / N)) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (2 * c * L) := by
          apply Real.exp_le_exp.mpr
          have := mul_le_mul_of_nonneg_right hmL hγnn
          calc (m : ℝ) * (2 * c / N) ≤ L * N * (2 * c / N) := this
            _ = 2 * c * L := by field_simp
  have hfar : ((m : ℝ≥0∞) * ENNReal.ofReal (2 * (A * (δ + 1 / K) + c * η))
      * (1 + ENNReal.ofReal (2 * c / N)) ^ m) / ENNReal.ofReal D ≤ ENNReal.ofReal e₁ := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm,
      ← ENNReal.ofReal_add zero_le_one hγnn, ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_div_of_pos hDp]
    apply ENNReal.ofReal_le_ofReal
    rw [div_le_iff₀ hDp]
    calc (m : ℝ) * (2 * (A * (δ + 1 / K) + c * η)) * (1 + 2 * c / N) ^ m
        ≤ (L * N) * β₀ * Real.exp (2 * c * L) :=
          mul_le_mul (mul_le_mul hmL hβ hβnn (by positivity)) hpow (by positivity) (by positivity)
      _ = e₁ * D := by rw [hβ₀, hD]; field_simp
  -- the event inclusion
  have hsub : Prod.fst ⁻¹' {ω | ENNReal.ofReal ε ≤
        PowerOfDUniversality.Fluid.supDistL1 (occPath (Y N) (τ N) ω) s T}
      ⊆ {p : Ω × EE | ENNReal.ofReal (ε / 2) ≤ PowerOfDUniversality.Fluid.supDistL1
            (occPath (Zc z₀ Y N) (fun k p => τ N k p.1) p) s T}
        ∪ Prod.fst ⁻¹' {ω | (∑ k ∈ Finset.range (m + 1), τ N k) ω ≤ T}
        ∪ Prod.fst ⁻¹' {ω | ¬ ∀ k, 0 ≤ τ N k ω}
        ∪ {p : Ω × EE | ¬ ∀ n ≤ m, Dist (Y N n p.1) (Zc z₀ Y N n p) ≤ D} := by
    intro p hp
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hp
    by_contra hno
    simp only [Set.mem_union, Set.mem_preimage, Set.mem_setOf_eq, not_or, not_le, not_not,
      Finset.sum_apply] at hno
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hno
    have hmm : ∀ t ∈ Set.Icc 0 T, epochCount (fun k => τ N k p.1) t ≤ m :=
      fun t ht => SC77K3EC.epoch_le (fun k => τ N k p.1) h3 T m h2 t ht.2
    have hcmp := SC77K3EC.sup_compare (fun n q => Y N n q.1) (Zc z₀ Y N) (fun k q => τ N k q.1)
      p s T m D hmm h4
    have hDN : D / N = ε / 2 := by rw [hD]; field_simp
    rw [hDN] at hcmp
    have hlt := ENNReal.add_lt_add_right (ENNReal.ofReal_ne_top (r := ε / 2)) h1
    rw [← ENNReal.ofReal_add (by linarith) (by linarith), add_halves] at hlt
    exact absurd (hp.trans hcmp) (not_le.mpr hlt)
  calc P {ω | ENNReal.ofReal ε ≤
        PowerOfDUniversality.Fluid.supDistL1 (occPath (Y N) (τ N) ω) s T}
      = (P.prod (nu lam d M G hlam hd)) (Prod.fst ⁻¹' {ω | ENNReal.ofReal ε ≤
        PowerOfDUniversality.Fluid.supDistL1 (occPath (Y N) (τ N) ω) s T}) := (hfst _).symm
    _ ≤ _ := measure_mono hsub
    _ ≤ _ := (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
          (add_le_add (measure_union_le _ _) le_rfl)) le_rfl)
    _ ≤ ENNReal.ofReal e₁ + ENNReal.ofReal e₁ + 0 + ENNReal.ofReal e₁ := by
        refine add_le_add (add_le_add (add_le_add hN1 ?_) ?_) (hE4.trans hfar)
        · rw [hfst]; exact hE2
        · rw [hfst, hE3]
    _ = ENNReal.ofReal r0 := by
        rw [add_zero, ← ENNReal.ofReal_add he₁p.le he₁p.le,
          ← ENNReal.ofReal_add (by positivity) he₁p.le, he₁]
        congr 1
        ring
    _ ≤ e := hr0e.le

end SC77K3H

open StrictCompatLB.MeanField in
theorem solution : ∀ (lam : ℝ), 0 < lam → lam < 1 → ∀ (d : ℕ), 2 ≤ d →
  ∀ (M : ℕ → ℕ), (∀ N, 0 < M N) → ∀ (G : (N : ℕ) → Finset (Fin N × Fin (M N))),
  IsConnectedSeq M G → IsPropSparse M G →
  ∀ (z₀ : (N : ℕ) → Fin N → ℕ) (s : ℝ → ℕ → ℝ) (T : ℝ), 0 ≤ T →
  (∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (Y : (N : ℕ) → ℕ → Ω → (Fin N → ℕ)) (τ : ℕ → ℕ → Ω → ℝ),
      (∀ N, 1 ≤ N → IsLBProcess P lam M N (piRoute M G N (jsqdAssign d)) (z₀ N) (Y N) (τ N)) →
      ∀ ε : ℝ, 0 < ε → Tendsto (fun N => P {ω | ENNReal.ofReal ε ≤
          PowerOfDUniversality.Fluid.supDistL1 (occPath (Y N) (τ N) ω) s T}) atTop (𝓝 0)) →
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (Y : (N : ℕ) → ℕ → Ω → (Fin N → ℕ)) (τ : ℕ → ℕ → Ω → ℝ),
      (∀ N, 1 ≤ N → IsLBProcess P lam M N (jsqdRoute M G N d) (z₀ N) (Y N) (τ N)) →
      ∀ ε : ℝ, 0 < ε → Tendsto (fun N => P {ω | ENNReal.ofReal ε ≤
          PowerOfDUniversality.Fluid.supDistL1 (occPath (Y N) (τ N) ω) s T}) atTop (𝓝 0) := by
  exact SC77K3H.k3
