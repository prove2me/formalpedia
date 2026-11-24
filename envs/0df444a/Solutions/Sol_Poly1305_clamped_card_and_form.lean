-- Prove2me | solution 1 for Poly1305.clamped_card_and_form
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-24T08:05:01.700598+00:00
-- url     : https://prove2.me/submissions/1b96d9dc-7fd9-4c20-b111-5c83f7b230c2

import Definitions.Def_Poly1305Bernstein
import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Fin

section
section
namespace Poly1305.DefsClamp

theorem leVal_expand (r : Str16) : leVal r =
    1 * (r 0 : ℕ) + 2 ^ 8 * (r 1 : ℕ) + 2 ^ 16 * (r 2 : ℕ) + 2 ^ 24 * (r 3 : ℕ) +
    2 ^ 32 * (r 4 : ℕ) + 2 ^ 40 * (r 5 : ℕ) + 2 ^ 48 * (r 6 : ℕ) + 2 ^ 56 * (r 7 : ℕ) +
    2 ^ 64 * (r 8 : ℕ) + 2 ^ 72 * (r 9 : ℕ) + 2 ^ 80 * (r 10 : ℕ) + 2 ^ 88 * (r 11 : ℕ) +
    2 ^ 96 * (r 12 : ℕ) + 2 ^ 104 * (r 13 : ℕ) + 2 ^ 112 * (r 14 : ℕ) + 2 ^ 120 * (r 15 : ℕ) := by
  simp only [leVal, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp only [add_assoc]
  rfl

theorem sum_digits (n k : ℕ) :
    ∑ j ∈ Finset.range k, 2 ^ (8 * j) * (n / 2 ^ (8 * j) % 256) = n % 2 ^ (8 * k) := by
  induction k with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, show 8 * (k + 1) = 8 * k + 8 by ring, pow_add,
      Nat.mod_mul]
    norm_num

theorem leVal_toStr16 (n : ℕ) : leVal (toStr16 n) = n % 2 ^ 128 := by
  unfold leVal toStr16
  simp only
  rw [Fin.sum_univ_eq_sum_range (fun j => 2 ^ (8 * j) * (n / 2 ^ (8 * j) % 256)) 16]
  exact sum_digits n 16

theorem toStr16_val (n : ℕ) (j : Fin 16) : (toStr16 n j : ℕ) = n / 2 ^ (8 * (j : ℕ)) % 256 :=
  rfl

theorem form (n : ℕ) : (∃ r : Str16, IsClamped r ∧ leVal r = n) ↔
      ∃ r₀ r₁ r₂ r₃ : ℕ, n = r₀ + r₁ + r₂ + r₃ ∧ r₀ < 2 ^ 28 ∧
        (∃ k ∈ Finset.range (2 ^ 26), r₁ = 2 ^ 32 * (4 * k)) ∧
        (∃ k ∈ Finset.range (2 ^ 26), r₂ = 2 ^ 64 * (4 * k)) ∧
        (∃ k ∈ Finset.range (2 ^ 26), r₃ = 2 ^ 96 * (4 * k)) := by
  constructor
  · rintro ⟨r, ⟨h3, h7, h11, h15, h4, h8, h12⟩, rfl⟩
    rw [leVal_expand]
    have b0 := (r 0).isLt; have b1 := (r 1).isLt; have b2 := (r 2).isLt
    have b5 := (r 5).isLt; have b6 := (r 6).isLt; have b9 := (r 9).isLt
    have b10 := (r 10).isLt; have b13 := (r 13).isLt; have b14 := (r 14).isLt
    have b4 := (r 4).isLt; have b8 := (r 8).isLt; have b12 := (r 12).isLt
    generalize (r 0 : ℕ) = a0 at *; generalize (r 1 : ℕ) = a1 at *
    generalize (r 2 : ℕ) = a2 at *; generalize (r 3 : ℕ) = a3 at *
    generalize (r 4 : ℕ) = a4 at *; generalize (r 5 : ℕ) = a5 at *
    generalize (r 6 : ℕ) = a6 at *; generalize (r 7 : ℕ) = a7 at *
    generalize (r 8 : ℕ) = a8 at *; generalize (r 9 : ℕ) = a9 at *
    generalize (r 10 : ℕ) = a10 at *; generalize (r 11 : ℕ) = a11 at *
    generalize (r 12 : ℕ) = a12 at *; generalize (r 13 : ℕ) = a13 at *
    generalize (r 14 : ℕ) = a14 at *; generalize (r 15 : ℕ) = a15 at *
    refine ⟨a0 + 2 ^ 8 * a1 + 2 ^ 16 * a2 + 2 ^ 24 * a3,
      2 ^ 32 * (4 * (a4 / 4 + 2 ^ 6 * a5 + 2 ^ 14 * a6 + 2 ^ 22 * a7)),
      2 ^ 64 * (4 * (a8 / 4 + 2 ^ 6 * a9 + 2 ^ 14 * a10 + 2 ^ 22 * a11)),
      2 ^ 96 * (4 * (a12 / 4 + 2 ^ 6 * a13 + 2 ^ 14 * a14 + 2 ^ 22 * a15)),
      ?_, ?_, ⟨_, ?_, rfl⟩, ⟨_, ?_, rfl⟩, ⟨_, ?_, rfl⟩⟩
    · norm_num; omega
    · norm_num; omega
    · rw [Finset.mem_range]; norm_num; omega
    · rw [Finset.mem_range]; norm_num; omega
    · rw [Finset.mem_range]; norm_num; omega
  · rintro ⟨r₀, r₁, r₂, r₃, rfl, h0, ⟨k1, hk1, rfl⟩, ⟨k2, hk2, rfl⟩, ⟨k3, hk3, rfl⟩⟩
    rw [Finset.mem_range] at hk1 hk2 hk3
    refine ⟨toStr16 (r₀ + 2 ^ 32 * (4 * k1) + 2 ^ 64 * (4 * k2) + 2 ^ 96 * (4 * k3)),
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals
      first
      | (rw [leVal_toStr16]; apply Nat.mod_eq_of_lt; norm_num at h0 hk1 hk2 hk3 ⊢; omega)
      | (rw [toStr16_val]; norm_num at h0 hk1 hk2 hk3 ⊢; omega)

/-- The four-part parametrization. -/
def f (x : ℕ × ℕ × ℕ × ℕ) : ℕ :=
  x.1 + 2 ^ 32 * (4 * x.2.1) + 2 ^ 64 * (4 * x.2.2.1) + 2 ^ 96 * (4 * x.2.2.2)

/-- The parameter box. -/
def T : Finset (ℕ × ℕ × ℕ × ℕ) :=
  Finset.range (2 ^ 28) ×ˢ Finset.range (2 ^ 26) ×ˢ Finset.range (2 ^ 26) ×ˢ
    Finset.range (2 ^ 26)

set_option linter.constructorNameAsVariable false in
theorem set_eq : {n : ℕ | ∃ r : Str16, IsClamped r ∧ leVal r = n} = ↑(T.image f) := by
  ext n
  rw [Set.mem_ofPred_eq, form, Finset.coe_image, Set.mem_image]
  constructor
  · rintro ⟨r₀, r₁, r₂, r₃, rfl, h0, ⟨k1, hk1, rfl⟩, ⟨k2, hk2, rfl⟩, ⟨k3, hk3, rfl⟩⟩
    refine ⟨(r₀, k1, k2, k3), ?_, rfl⟩
    simp only [T, Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hk1 hk2 hk3 ⊢
    exact ⟨h0, hk1, hk2, hk3⟩
  · rintro ⟨⟨a, b, c, d⟩, hx, rfl⟩
    simp only [T, Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hx
    exact ⟨a, _, _, _, rfl, hx.1, ⟨b, Finset.mem_range.mpr hx.2.1, rfl⟩,
      ⟨c, Finset.mem_range.mpr hx.2.2.1, rfl⟩, ⟨d, Finset.mem_range.mpr hx.2.2.2, rfl⟩⟩

set_option linter.constructorNameAsVariable false in
theorem injOn : Set.InjOn f ↑T := by
  rintro ⟨a, b, c, d⟩ hx ⟨a', b', c', d'⟩ hy he
  simp only [T, Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hx hy
  simp only [f] at he
  norm_num at hx hy he
  have : a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by omega
  obtain ⟨rfl, rfl, rfl, rfl⟩ := this
  rfl

end Poly1305.DefsClamp

namespace Poly1305

theorem clamped_card_and_form_dev :
    {n : ℕ | ∃ r : Str16, IsClamped r ∧ leVal r = n}.ncard = 2 ^ 106 ∧
    ∀ n : ℕ, (∃ r : Str16, IsClamped r ∧ leVal r = n) ↔
      ∃ r₀ r₁ r₂ r₃ : ℕ, n = r₀ + r₁ + r₂ + r₃ ∧ r₀ < 2 ^ 28 ∧
        (∃ k ∈ Finset.range (2 ^ 26), r₁ = 2 ^ 32 * (4 * k)) ∧
        (∃ k ∈ Finset.range (2 ^ 26), r₂ = 2 ^ 64 * (4 * k)) ∧
        (∃ k ∈ Finset.range (2 ^ 26), r₃ = 2 ^ 96 * (4 * k)) := by
  refine ⟨?_, DefsClamp.form⟩
  rw [DefsClamp.set_eq, Set.ncard_coe_finset, Finset.card_image_of_injOn DefsClamp.injOn]
  simp only [DefsClamp.T, Finset.card_product, Finset.card_range]
  norm_num

end Poly1305

end
end

section
open Poly1305

theorem solution :
    {n : ℕ | ∃ r : Str16, IsClamped r ∧ leVal r = n}.ncard = 2 ^ 106 ∧
    ∀ n : ℕ, (∃ r : Str16, IsClamped r ∧ leVal r = n) ↔
      ∃ r₀ r₁ r₂ r₃ : ℕ, n = r₀ + r₁ + r₂ + r₃ ∧ r₀ < 2 ^ 28 ∧
        (∃ k ∈ Finset.range (2 ^ 26), r₁ = 2 ^ 32 * (4 * k)) ∧
        (∃ k ∈ Finset.range (2 ^ 26), r₂ = 2 ^ 64 * (4 * k)) ∧
        (∃ k ∈ Finset.range (2 ^ 26), r₃ = 2 ^ 96 * (4 * k)) := by
  apply Poly1305.clamped_card_and_form_dev <;> assumption

end
