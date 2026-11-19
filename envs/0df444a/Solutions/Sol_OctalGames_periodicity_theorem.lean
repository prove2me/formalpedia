-- Prove2me | solution 1 for OctalGames.periodicity_theorem
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T17:54:35.862243+00:00
-- url     : https://prove2.me/submissions/65f34581-d4ca-433b-bfc8-51927eeed1cd

import Mathlib
import Definitions.Def_OctalGames_Code

open OctalGames

namespace OctalPeriodicityProof

theorem table_length (c : Code) (n : ℕ) : (table c n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [table, ih]

theorem table_getD_succ (c : Code) {m n : ℕ} (hm : m < n) :
    (table c (n + 1)).getD m 0 = (table c n).getD m 0 := by
  simp only [table, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by rw [table_length]; exact hm)]

theorem table_getD_mono (c : Code) {m n : ℕ} (hm : m < n) :
    ∀ N, n ≤ N → (table c N).getD m 0 = (table c n).getD m 0 := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => rfl
  | succ N hN ih => rw [table_getD_succ c (lt_of_lt_of_le hm hN), ih]

theorem table_getD_last (c : Code) (n : ℕ) :
    (table c (n + 1)).getD n 0 = mex (optionValues c (fun m => (table c n).getD m 0) n) := by
  simp only [table, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by rw [table_length])]
  simp [table_length]

theorem grundy_eq_table (c : Code) {m N : ℕ} (hm : m < N) : grundy c m = (table c N).getD m 0 := by
  unfold grundy
  rw [table_getD_mono c (Nat.lt_succ_self m) N hm]

theorem mem_optionValues (c : Code) (g : ℕ → ℕ) (n v : ℕ) :
    v ∈ optionValues c g n ↔
      (1 ≤ n ∧ c.bit n 0 = true ∧ v = 0) ∨
      (∃ i, 1 ≤ i ∧ i < n ∧ c.bit i 1 = true ∧ g (n - i) = v) ∨
      (∃ a b, 1 ≤ a ∧ a < n ∧ 1 ≤ b ∧ b < n ∧ a + b ≤ n ∧ c.bit (n - (a + b)) 2 = true ∧
        g a ^^^ g b = v) := by
  unfold optionValues
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_Ico,
    Finset.mem_product, Prod.exists]
  constructor
  · rintro ((h | ⟨i, ⟨⟨h1, h2⟩, h3⟩, h4⟩) | ⟨a, b, ⟨⟨⟨ha1, ha2⟩, hb1, hb2⟩, hab, hbit⟩, hv⟩)
    · split_ifs at h with hc
      · exact Or.inl ⟨hc.1, hc.2, Finset.mem_singleton.mp h⟩
      · simp at h
    · exact Or.inr (Or.inl ⟨i, h1, h2, h3, h4⟩)
    · exact Or.inr (Or.inr ⟨a, b, ha1, ha2, hb1, hb2, hab, hbit, hv⟩)
  · rintro (⟨h1, h2, h3⟩ | ⟨i, h1, h2, h3, h4⟩ | ⟨a, b, ha1, ha2, hb1, hb2, hab, hbit, hv⟩)
    · left; left; rw [if_pos ⟨h1, h2⟩]; exact Finset.mem_singleton.mpr h3
    · left; right; exact ⟨i, ⟨⟨h1, h2⟩, h3⟩, h4⟩
    · right; exact ⟨a, b, ⟨⟨⟨ha1, ha2⟩, hb1, hb2⟩, hab, hbit⟩, hv⟩

theorem optionValues_congr (c : Code) {g g' : ℕ → ℕ} {n : ℕ} (h : ∀ m, m < n → g m = g' m) :
    optionValues c g n = optionValues c g' n := by
  ext v
  rw [mem_optionValues, mem_optionValues]
  constructor
  · rintro (h0 | ⟨i, h1, h2, h3, h4⟩ | ⟨a, b, ha1, ha2, hb1, hb2, hab, hbit, hv⟩)
    · exact Or.inl h0
    · exact Or.inr (Or.inl ⟨i, h1, h2, h3, by rw [← h _ (by omega)]; exact h4⟩)
    · exact Or.inr (Or.inr ⟨a, b, ha1, ha2, hb1, hb2, hab, hbit, by rw [← h a ha2, ← h b hb2]; exact hv⟩)
  · rintro (h0 | ⟨i, h1, h2, h3, h4⟩ | ⟨a, b, ha1, ha2, hb1, hb2, hab, hbit, hv⟩)
    · exact Or.inl h0
    · exact Or.inr (Or.inl ⟨i, h1, h2, h3, by rw [h _ (by omega)]; exact h4⟩)
    · exact Or.inr (Or.inr ⟨a, b, ha1, ha2, hb1, hb2, hab, hbit, by rw [h a ha2, h b hb2]; exact hv⟩)

/-- The mex rule for `grundy`. -/
theorem grundy_eq (c : Code) (n : ℕ) : grundy c n = mex (optionValues c (grundy c) n) := by
  unfold grundy
  rw [table_getD_last]
  congr 1
  apply optionValues_congr
  intro m hm
  exact table_getD_mono c (Nat.lt_succ_self m) n hm

theorem bit_eq_false (c : Code) {i : ℕ} (j : ℕ) (h : c.digit i = 0) : c.bit i j = false := by
  simp [Code.bit, h]

end OctalPeriodicityProof

open OctalPeriodicityProof in
theorem solution (c : Code) (k n₀ p : ℕ) (hk : ∀ i, k < i → c.digit i = 0) (hn₀ : 1 ≤ n₀) (hp : 1 ≤ p) (h : ∀ n, n₀ ≤ n → n < 2 * n₀ + p + k → grundy c (n + p) = grundy c n) : ∀ n, n₀ ≤ n → grundy c (n + p) = grundy c n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  by_cases hsmall : n < 2 * n₀ + p + k
  · exact h n hn hsmall
  replace hsmall : 2 * n₀ + p + k ≤ n := by omega
  -- a set bit at index `i` forces `i ≤ k`
  have hbit : ∀ i j, c.bit i j = true → i ≤ k := by
    intro i j hij
    by_contra hlt
    rw [bit_eq_false c j (hk i (by omega))] at hij
    exact Bool.false_ne_true hij
  rw [grundy_eq c (n + p), grundy_eq c n]
  congr 1
  ext v
  rw [mem_optionValues, mem_optionValues]
  constructor
  · rintro (⟨h1, h2, _⟩ | ⟨i, h1, h2, h3, h4⟩ | ⟨a, b, ha1, ha2, hb1, hb2, hab, hb, hv⟩)
    · have := hbit _ _ h2; omega
    · have hik := hbit _ _ h3
      refine Or.inr (Or.inl ⟨i, h1, by omega, h3, ?_⟩)
      rw [← h4, show n + p - i = (n - i) + p by omega]
      exact (ih (n - i) (by omega) (by omega)).symm
    · have hik := hbit _ _ hb
      refine Or.inr (Or.inr ?_)
      by_cases hbig : n₀ + p ≤ b
      · refine ⟨a, b - p, ha1, by omega, by omega, by omega, by omega,
          by rw [show n - (a + (b - p)) = n + p - (a + b) by omega]; exact hb, ?_⟩
        rw [← hv]
        have := ih (b - p) (by omega) (by omega)
        rw [show b - p + p = b by omega] at this
        rw [this]
      · refine ⟨a - p, b, by omega, by omega, hb1, by omega, by omega,
          by rw [show n - (a - p + b) = n + p - (a + b) by omega]; exact hb, ?_⟩
        rw [← hv]
        have := ih (a - p) (by omega) (by omega)
        rw [show a - p + p = a by omega] at this
        rw [this]
  · rintro (⟨h1, h2, _⟩ | ⟨i, h1, h2, h3, h4⟩ | ⟨a, b, ha1, ha2, hb1, hb2, hab, hb, hv⟩)
    · have := hbit _ _ h2; omega
    · have hik := hbit _ _ h3
      refine Or.inr (Or.inl ⟨i, h1, by omega, h3, ?_⟩)
      rw [← h4, show n + p - i = (n - i) + p by omega]
      exact ih (n - i) (by omega) (by omega)
    · have hik := hbit _ _ hb
      refine Or.inr (Or.inr ?_)
      by_cases hbig : n₀ ≤ b
      · refine ⟨a, b + p, ha1, by omega, by omega, by omega, by omega,
          by rw [show n + p - (a + (b + p)) = n - (a + b) by omega]; exact hb, ?_⟩
        rw [← hv, ih b (by omega) hbig]
      · refine ⟨a + p, b, by omega, by omega, hb1, by omega, by omega,
          by rw [show n + p - (a + p + b) = n - (a + b) by omega]; exact hb, ?_⟩
        rw [← hv, ih a (by omega) (by omega)]
