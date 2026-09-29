-- Prove2me | solution 1 for ValuationSubring.exists_aeval_div_eq_aeval_div_add_inv_pow_mul_add_aeval_inv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/d35c6261-e1fe-560a-9bde-30f88b087083

import Mathlib
import Theorems.Thm_ValuationSubring_exists_aeval_div_eq_aeval_div_add_aeval_inv_div
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_aeval_div_eq_aeval_div_add_inv_pow_mul_add_aeval_inv

open Polynomial

namespace E4Sol

variable {L : Type*} [Field L] (A : ValuationSubring L)

def ACoeff (p : L[X]) : Prop := ∀ j, p.coeff j ∈ A

theorem ACoeff.zero : ACoeff A (0 : L[X]) := fun j => by simp [A.zero_mem]

theorem ACoeff.C {a : L} (ha : a ∈ A) : ACoeff A (C a) := fun j => by
  rw [coeff_C]; split_ifs <;> simp [ha, A.zero_mem]

theorem ACoeff.X : ACoeff A (X : L[X]) := fun j => by
  rw [coeff_X]; split_ifs <;> simp [A.one_mem, A.zero_mem]

theorem ACoeff.X_pow (n : ℕ) : ACoeff A ((Polynomial.X : L[X]) ^ n) := fun j => by
  rw [coeff_X_pow]; split_ifs <;> simp [A.one_mem, A.zero_mem]

theorem ACoeff.add {p q : L[X]} (hp : ACoeff A p) (hq : ACoeff A q) : ACoeff A (p + q) :=
  fun j => by rw [coeff_add]; exact add_mem (hp j) (hq j)

theorem ACoeff.sub {p q : L[X]} (hp : ACoeff A p) (hq : ACoeff A q) : ACoeff A (p - q) :=
  fun j => by rw [coeff_sub]; exact sub_mem (hp j) (hq j)

theorem ACoeff.mul {p q : L[X]} (hp : ACoeff A p) (hq : ACoeff A q) : ACoeff A (p * q) := by
  intro j
  rw [coeff_mul]
  refine sum_mem fun x _ => ?_
  exact mul_mem (hp _) (hq _)

theorem ACoeff.divX {p : L[X]} (hp : ACoeff A p) : ACoeff A (divX p) :=
  fun j => by rw [coeff_divX]; exact hp _

theorem ACoeff.valuation_le {p : L[X]} (hp : ACoeff A p) (j : ℕ) :
    A.valuation (p.coeff j) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (hp j)

def IsGood (t : L[X]) : Prop :=
  A.valuation (t.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t.coeff j) < 1

theorem IsGood.valuation_le {t : L[X]} (ht : IsGood A t) (j : ℕ) :
    A.valuation (t.coeff j) ≤ 1 := by
  by_cases hj : j = 0
  · rw [hj, ht.1]
  · exact (ht.2 j hj).le

theorem IsGood.acoeff {t : L[X]} (ht : IsGood A t) : ACoeff A t :=
  fun j => (A.valuation_le_one_iff _).mp (ht.valuation_le A j)

theorem IsGood.coeff_zero_ne {t : L[X]} (ht : IsGood A t) : t.coeff 0 ≠ 0 := by
  intro h; have := ht.1; rw [h, map_zero] at this; exact zero_ne_one this

theorem IsGood.ne_zero {t : L[X]} (ht : IsGood A t) : t ≠ 0 := fun h =>
  ht.coeff_zero_ne A (by rw [h, coeff_zero])

theorem aeval_ne_zero_of_isGood {F : Type*} [Field F] [Algebra L F] {g : F}
    (hg : Transcendental L g) {t : L[X]} (ht : IsGood A t) : aeval g t ≠ 0 := fun h =>
  ht.ne_zero A (transcendental_iff_injective.mp hg (by rw [h, map_zero]))

variable {F : Type*} [Field F] [Algebra L F]

def IsLam (g x : F) : Prop :=
  ∃ p t : L[X], ACoeff A p ∧ IsGood A t ∧ x * aeval g t = aeval g p

theorem IsLam.exists_eq_add_mul {g x : F} (hg : Transcendental L g) (hx : IsLam A g x) :
    ∃ a ∈ A, ∃ x', IsLam A g x' ∧ x = algebraMap L F a + g * x' := by
  obtain ⟨p, t, hp, ht, hxe⟩ := hx
  have ht0 := ht.coeff_zero_ne A
  have hat := aeval_ne_zero_of_isGood A hg ht
  set a : L := p.coeff 0 * (t.coeff 0)⁻¹ with ha
  have haA : a ∈ A := by
    rw [← A.valuation_le_one_iff, ha, map_mul, map_inv₀, ht.1, inv_one, mul_one]
    exact hp.valuation_le A 0
  set p' : L[X] := divX (p - Polynomial.C a * t) with hp'
  have hp'A : ACoeff A p' :=
    ACoeff.divX A (ACoeff.sub A hp (ACoeff.mul A (ACoeff.C A haA) (ht.acoeff A)))
  have hzero : (p - Polynomial.C a * t).coeff 0 = 0 := by
    rw [coeff_sub, coeff_C_mul, ha, inv_mul_cancel_right₀ ht0, sub_self]
  have hdecomp : X * p' = p - Polynomial.C a * t := by
    have := X_mul_divX_add (p - Polynomial.C a * t)
    rw [hzero, C_0, add_zero] at this
    exact this
  refine ⟨a, haA, aeval g p' / aeval g t, ⟨p', t, hp'A, ht, div_mul_cancel₀ _ hat⟩, ?_⟩
  have h1 : aeval g (X * p') = aeval g (p - Polynomial.C a * t) := by rw [hdecomp]
  simp only [map_mul, aeval_X, map_sub, aeval_C] at h1
  field_simp
  linear_combination hxe - h1

theorem IsLam.exists_eq_aeval_add_pow_mul {g x : F} (hg : Transcendental L g)
    (hx : IsLam A g x) (m : ℕ) :
    ∃ r : L[X], ACoeff A r ∧ r.degree < m ∧ ∃ x', IsLam A g x' ∧ x = aeval g r + g ^ m * x' := by
  induction m with
  | zero =>
    exact ⟨0, ACoeff.zero A, by simp, x, hx, by simp⟩
  | succ m ih =>
    obtain ⟨r, hr, hrdeg, x', hx', hxe⟩ := ih
    obtain ⟨a, haA, x'', hx'', hx'e⟩ := hx'.exists_eq_add_mul A hg
    refine ⟨r + Polynomial.C a * X ^ m, ACoeff.add A hr (ACoeff.mul A (ACoeff.C A haA)
      (ACoeff.X_pow A m)), ?_, x'', hx'', ?_⟩
    · refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
      · exact lt_of_lt_of_le hrdeg (by exact_mod_cast Nat.le_succ m)
      · calc (Polynomial.C a * X ^ m).degree ≤ (m : WithBot ℕ) := degree_C_mul_X_pow_le m a
          _ < ((m + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_self m
    · rw [hxe, hx'e]
      simp only [map_add, map_mul, aeval_C, aeval_X_pow]
      ring

end E4Sol

open E4Sol in
theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] {f : F} (hf : Transcendental L f)
    (p t : L[X]) (hp : ∀ j, p.coeff j ∈ A)
    (ht : ∃ d, A.valuation (t.coeff d) = 1 ∧ ∀ j, j ≠ d → A.valuation (t.coeff j) < 1)
    (m : ℕ) :
    ∃ p₁ t₁ q s r : L[X],
      (∀ j, p₁.coeff j ∈ A) ∧ (∀ j, q.coeff j ∈ A) ∧ (∀ j, r.coeff j ∈ A) ∧ r.degree < m ∧
      (A.valuation (t₁.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t₁.coeff j) < 1) ∧
      (A.valuation (s.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (s.coeff j) < 1) ∧
      aeval f p / aeval f t =
        aeval f p₁ / aeval f t₁ + (f⁻¹) ^ m * (aeval f⁻¹ q / aeval f⁻¹ s) + aeval f⁻¹ r := by
  have hfi : Transcendental L f⁻¹ := fun h => hf (IsAlgebraic.inv_iff.mp h)
  obtain ⟨p₁, t₁, q₀, s₀, hp₁, hq₀, ht₁, hs₀, hdec⟩ :=
    ValuationSubring.exists_aeval_div_eq_aeval_div_add_aeval_inv_div A hf p t hp ht

  have hlam : IsLam A f⁻¹ (aeval f⁻¹ q₀ / aeval f⁻¹ s₀) :=
    ⟨q₀, s₀, hq₀, hs₀, div_mul_cancel₀ _ (aeval_ne_zero_of_isGood A hfi hs₀)⟩
  obtain ⟨r, hr, hrdeg, x', ⟨q, s, hq, hs, hx'e⟩, hxe⟩ := hlam.exists_eq_aeval_add_pow_mul A hfi m
  refine ⟨p₁, t₁, q, s, r, hp₁, hq, hr, hrdeg, ht₁, hs, ?_⟩
  rw [hdec, hxe, eq_div_iff (aeval_ne_zero_of_isGood A hfi hs) |>.mpr hx'e]
  ring

end S_ValuationSubring_exists_aeval_div_eq_aeval_div_add_inv_pow_mul_add_aeval_inv
end P2MW
export P2MW.S_ValuationSubring_exists_aeval_div_eq_aeval_div_add_inv_pow_mul_add_aeval_inv (solution)
