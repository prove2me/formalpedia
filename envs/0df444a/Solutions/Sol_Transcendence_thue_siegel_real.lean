-- Prove2me | solution 1 for Transcendence.thue_siegel_real
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-02T10:12:21.043381+00:00
-- url     : https://prove2.me/submissions/9a883bc2-419a-49d9-9a65-0b5bceed6afb

import Mathlib

/-!
# Thue–Siegel by the box principle (Waldschmidt, DALAG Lemma 4.11)

The vectors `ξ ∈ {0, …, X}^Λ` are sorted into `ℓ^μ` boxes by the clamped floors of the shifted,
rescaled forms `s_j(ξ) = (Σ_λ v_{jλ} ξ_λ + X Σ_λ max(0, -v_{jλ})) / h`, `h = C X / ℓ`, which lie in
`[0, ℓ]`. As `ℓ^μ < (X + 1)^ν`, two vectors share a box, and their difference is the solution.
Unlike the book's `U`, the bound `C` need not be an integer.
-/

namespace ThueSiegelReal

/-- Two reals in `[0, ℓ]` with the same clamped floor are at distance at most one. -/
lemma abs_sub_le_one_of_cell {ℓ : ℕ} (hℓ : 0 < ℓ) {a b : ℝ} (ha0 : 0 ≤ a) (haℓ : a ≤ ℓ)
    (hb0 : 0 ≤ b) (hbℓ : b ≤ ℓ) (h : min ⌊a⌋₊ (ℓ - 1) = min ⌊b⌋₊ (ℓ - 1)) : |a - b| ≤ 1 := by
  have key : ∀ x : ℝ, 0 ≤ x → x ≤ ℓ →
      ((min ⌊x⌋₊ (ℓ - 1) : ℕ) : ℝ) ≤ x ∧ x ≤ ((min ⌊x⌋₊ (ℓ - 1) : ℕ) : ℝ) + 1 := by
    intro x hx0 hxℓ
    constructor
    · calc ((min ⌊x⌋₊ (ℓ - 1) : ℕ) : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast min_le_left _ _
        _ ≤ x := Nat.floor_le hx0
    · rcases le_total ⌊x⌋₊ (ℓ - 1) with h1 | h1
      · rw [min_eq_left h1]; exact (Nat.lt_floor_add_one x).le
      · rw [min_eq_right h1]
        have : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
          rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hℓ.ne')]; simp
        rw [this]; linarith
  obtain ⟨ha1, ha2⟩ := key a ha0 haℓ
  obtain ⟨hb1, hb2⟩ := key b hb0 hbℓ
  rw [h] at ha1 ha2
  rw [abs_le]; constructor <;> linarith

end ThueSiegelReal

theorem solution {J Λ : Type*} [Fintype J] [Fintype Λ] (v : J → Λ → ℝ) {C : ℝ}
    (hC : 0 < C) (hv : ∀ j, ∑ l, |v j l| ≤ C) {X ℓ : ℕ} (hℓ : 0 < ℓ)
    (hcard : ℓ ^ Fintype.card J < (X + 1) ^ Fintype.card Λ) :
    ∃ ξ : Λ → ℤ, ξ ≠ 0 ∧ (∀ l, |ξ l| ≤ X) ∧ ∀ j, |∑ l, v j l * ξ l| ≤ C * X / ℓ := by
  classical
  have hX : 0 < X := by
    rcases Nat.eq_zero_or_pos X with h | h
    · subst h
      have : 1 ≤ ℓ ^ Fintype.card J := Nat.one_le_pow _ _ hℓ
      simp at hcard
      omega
    · exact h
  set h : ℝ := C * X / ℓ with hh
  have hpos : 0 < h := by positivity
  let s : J → (Λ → Fin (X + 1)) → ℝ := fun j ξ =>
    (∑ l, (v j l * ((ξ l : ℕ) : ℝ) + X * max 0 (-v j l))) / h
  have hterm : ∀ j l (ξ : Λ → Fin (X + 1)),
      0 ≤ v j l * ((ξ l : ℕ) : ℝ) + X * max 0 (-v j l) ∧
        v j l * ((ξ l : ℕ) : ℝ) + X * max 0 (-v j l) ≤ X * |v j l| := by
    intro j l ξ
    have hξ0 : (0 : ℝ) ≤ ((ξ l : ℕ) : ℝ) := Nat.cast_nonneg _
    have hξX : ((ξ l : ℕ) : ℝ) ≤ X := by exact_mod_cast Nat.lt_succ_iff.mp (ξ l).isLt
    rcases le_total 0 (v j l) with hv0 | hv0
    · rw [max_eq_left (by linarith), abs_of_nonneg hv0]
      constructor <;> nlinarith
    · rw [max_eq_right (by linarith), abs_of_nonpos hv0]
      constructor <;> nlinarith
  have hs0 : ∀ j ξ, 0 ≤ s j ξ := fun j ξ =>
    div_nonneg (Finset.sum_nonneg fun l _ => (hterm j l ξ).1) hpos.le
  have hsℓ : ∀ j ξ, s j ξ ≤ ℓ := by
    intro j ξ
    rw [div_le_iff₀ hpos]
    calc ∑ l, (v j l * ((ξ l : ℕ) : ℝ) + X * max 0 (-v j l))
        ≤ ∑ l, (X : ℝ) * |v j l| := Finset.sum_le_sum fun l _ => (hterm j l ξ).2
      _ = X * ∑ l, |v j l| := by rw [Finset.mul_sum]
      _ ≤ X * C := mul_le_mul_of_nonneg_left (hv j) (Nat.cast_nonneg _)
      _ = ℓ * h := by rw [hh]; field_simp
  let f : (Λ → Fin (X + 1)) → (J → Fin ℓ) := fun ξ j =>
    ⟨min ⌊s j ξ⌋₊ (ℓ - 1), lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hℓ one_pos)⟩
  have hc : Fintype.card (J → Fin ℓ) < Fintype.card (Λ → Fin (X + 1)) := by
    simpa [Fintype.card_fun, Fintype.card_fin] using hcard
  obtain ⟨ξ₁, ξ₂, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hc
  refine ⟨fun l => ((ξ₁ l : ℕ) : ℤ) - ((ξ₂ l : ℕ) : ℤ), ?_, ?_, ?_⟩
  · intro h0
    apply hne
    funext l
    have := congrFun h0 l
    simp only [Pi.zero_apply, sub_eq_zero, Nat.cast_inj] at this
    exact Fin.ext this
  · intro l
    have h1 := (ξ₁ l).isLt
    have h2 := (ξ₂ l).isLt
    dsimp only
    rw [abs_le]
    constructor <;> omega
  · intro j
    have hcell : min ⌊s j ξ₁⌋₊ (ℓ - 1) = min ⌊s j ξ₂⌋₊ (ℓ - 1) := by
      have := congrFun heq j
      simp only [f, Fin.mk.injEq] at this
      exact this
    have h1 := ThueSiegelReal.abs_sub_le_one_of_cell hℓ (hs0 j ξ₁) (hsℓ j ξ₁) (hs0 j ξ₂)
      (hsℓ j ξ₂) hcell
    have hs : ∀ ξ : Λ → Fin (X + 1),
        h * s j ξ = ∑ l, (v j l * ((ξ l : ℕ) : ℝ) + X * max 0 (-v j l)) := by
      intro ξ
      simp only [s]
      field_simp
    have hsum : ∑ l, v j l * (((((ξ₁ l : ℕ) : ℤ) - ((ξ₂ l : ℕ) : ℤ) : ℤ)) : ℝ) =
        h * (s j ξ₁ - s j ξ₂) := by
      rw [mul_sub, hs, hs, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro l _
      push_cast
      ring
    rw [hsum, abs_mul, abs_of_pos hpos]
    calc h * |s j ξ₁ - s j ξ₂| ≤ h * 1 := mul_le_mul_of_nonneg_left h1 hpos.le
      _ = C * X / ℓ := by rw [mul_one]
