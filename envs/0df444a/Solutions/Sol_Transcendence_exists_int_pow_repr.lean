-- Prove2me | solution 1 for Transcendence.exists_int_pow_repr
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T16:44:34.971976+00:00
-- url     : https://prove2.me/submissions/9d02de7f-bded-42a8-b1d4-a07783c1240b

import Mathlib

/-!
Since `ℚ` is the fraction field of `ℤ`, `α` has a non-constant annihilator `m ∈ ℤ[X]`; let `d` be
its degree and `L ≠ 0` its leading coefficient. Put `r₀ = 1` and `r_{n+1} = L X rₙ - c m`, where
`c` is the coefficient of `X^{d-1}` in `rₙ`.
* Each `rₙ` has degree `< d`: the coefficient of `X^d` in `L X rₙ` is `Lc`, which the subtraction
  cancels, and all higher coefficients vanish.
* `rₙ(α) = Lⁿαⁿ`, by induction, since `m(α) = 0`.
* If `H` bounds the coefficients of `m` and `B` those of `rₙ`, the coefficients of `r_{n+1}` are at
  most `|L| B + B H`: those of `X rₙ` are coefficients of `rₙ` or `0`, and `|c| ≤ B`.
So `ℓ = d` and `A = |L| + H` work, with `r l` the coefficient of `X^l` in `rₙ`.
-/

namespace S7W3_exists_int_pow_repr

open Polynomial

/-- An algebraic number has a non-constant integer annihilator. -/
theorem exists_int_annihilator {K : Type*} [Field K] [CharZero K] {α : K}
    (hα : IsAlgebraic ℚ α) : ∃ m : ℤ[X], 0 < m.natDegree ∧ aeval α m = 0 := by
  obtain ⟨p, hp0, hpα⟩ := (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 hα
  refine ⟨p, Nat.pos_of_ne_zero fun h => ?_, hpα⟩
  rw [eq_C_of_natDegree_eq_zero h, aeval_C, eq_intCast (algebraMap ℤ K), Int.cast_eq_zero] at hpα
  exact hp0 (by rw [eq_C_of_natDegree_eq_zero h, hpα, map_zero C])

variable (m : ℤ[X])

/-- `Lⁿ Xⁿ` reduced modulo `m`, where `L` is the leading coefficient of `m`. -/
noncomputable def red : ℕ → ℤ[X]
  | 0 => 1
  | n + 1 => C m.leadingCoeff * X * red n - C ((red n).coeff (m.natDegree - 1)) * m

theorem red_natDegree (hd : 0 < m.natDegree) : ∀ n, (red m n).natDegree < m.natDegree
  | 0 => by
    rw [red, natDegree_one]
    exact hd
  | n + 1 => by
    have ih := red_natDegree hd n
    suffices h : (red m (n + 1)).natDegree ≤ m.natDegree - 1 by omega
    rw [natDegree_le_iff_coeff_eq_zero]
    intro j hj
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [red, coeff_sub, mul_assoc, coeff_C_mul, coeff_X_mul, coeff_C_mul]
    rcases Nat.lt_or_ge m.natDegree (j' + 1) with hgt | hle
    · rw [coeff_eq_zero_of_natDegree_lt hgt, coeff_eq_zero_of_natDegree_lt (by omega), mul_zero,
        mul_zero, sub_zero]
    · rw [show j' + 1 = m.natDegree by omega, coeff_natDegree,
        show j' = m.natDegree - 1 by omega]
      ring

theorem aeval_red {K : Type*} [Field K] {α : K} (hα : aeval α m = 0) :
    ∀ n, aeval α (red m n) = (m.leadingCoeff : K) ^ n * α ^ n
  | 0 => by rw [red, map_one (aeval (R := ℤ) α), pow_zero, pow_zero, one_mul]
  | n + 1 => by
    rw [red, map_sub (aeval (R := ℤ) α), map_mul (aeval (R := ℤ) α),
      map_mul (aeval (R := ℤ) α), map_mul (aeval (R := ℤ) α), aeval_C, aeval_C, aeval_X, hα,
      aeval_red hα n, mul_zero, sub_zero, eq_intCast (algebraMap ℤ K), pow_succ, pow_succ]
    ring

theorem coeff_red_le {H : ℕ} (hH : ∀ i, (m.coeff i).natAbs ≤ H) :
    ∀ n l, ((red m n).coeff l).natAbs ≤ (m.leadingCoeff.natAbs + H) ^ n
  | 0, l => by
    rw [red, coeff_one, pow_zero]
    split_ifs
    · rw [Int.natAbs_one]
    · rw [Int.natAbs_zero]
      exact Nat.zero_le 1
  | n + 1, l => by
    have ih := coeff_red_le hH n
    have hX : ((X * red m n).coeff l).natAbs ≤ (m.leadingCoeff.natAbs + H) ^ n := by
      cases l with
      | zero =>
        rw [coeff_X_mul_zero, Int.natAbs_zero]
        exact Nat.zero_le _
      | succ j =>
        rw [coeff_X_mul]
        exact ih j
    rw [red, coeff_sub, mul_assoc, coeff_C_mul, coeff_C_mul, pow_succ]
    refine (Int.natAbs_sub_le _ _).trans ?_
    rw [Int.natAbs_mul, Int.natAbs_mul]
    calc _ ≤ m.leadingCoeff.natAbs * (m.leadingCoeff.natAbs + H) ^ n
          + (m.leadingCoeff.natAbs + H) ^ n * H :=
          Nat.add_le_add (Nat.mul_le_mul le_rfl hX) (Nat.mul_le_mul (ih _) (hH l))
      _ = (m.leadingCoeff.natAbs + H) ^ n * (m.leadingCoeff.natAbs + H) := by ring

end S7W3_exists_int_pow_repr

open S7W3_exists_int_pow_repr Polynomial in
theorem solution {K : Type*} [Field K] [CharZero K] {α : K} (hα : IsAlgebraic ℚ α) :
    ∃ (ℓ A : ℕ) (L : ℤ), L ≠ 0 ∧ ∀ n : ℕ, ∃ r : ℕ → ℤ,
      (L : K) ^ n * α ^ n = ∑ l ∈ Finset.range ℓ, (r l : K) * α ^ l ∧
        ∀ l, (r l).natAbs ≤ A ^ n := by
  obtain ⟨m, hd, hmα⟩ := exists_int_annihilator hα
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [natDegree_zero] at hd
    exact lt_irrefl 0 hd
  have hH : ∀ i, (m.coeff i).natAbs ≤ ∑ j ∈ m.support, (m.coeff j).natAbs := by
    intro i
    by_cases hi : i ∈ m.support
    · exact Finset.single_le_sum (f := fun j => (m.coeff j).natAbs) (fun _ _ => Nat.zero_le _) hi
    · rw [notMem_support_iff.1 hi, Int.natAbs_zero]
      exact Nat.zero_le _
  refine ⟨m.natDegree, m.leadingCoeff.natAbs + ∑ j ∈ m.support, (m.coeff j).natAbs,
    m.leadingCoeff, leadingCoeff_ne_zero.2 hm0, fun n => ⟨(red m n).coeff, ?_, coeff_red_le m hH n⟩⟩
  rw [← aeval_red m hmα n, aeval_eq_sum_range' (red_natDegree m hd n)]
  simp only [zsmul_eq_mul]

#print axioms solution
