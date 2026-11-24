-- Prove2me | solution 1 for PrimePairSieve.twin_prime_constant_lower_131
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T20:09:01.919236+00:00
-- url     : https://prove2.me/submissions/5b8088c3-c5e0-453a-9fb0-fdbfd50b0bd2

import Mathlib
import Definitions.Def_TaoFivePrimes_SingularSeries
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

-- Adapted from andreaskapfer's accepted sieve_constants_certificate,
-- submission 91b4ca4a-771c-4be3-88cd-952059ec7610: same telescoping argument,
-- with cutoff 200 and a sharper independently checked rational lower product.
namespace ReciprocalSharperConstant
private lemma twinPartial_fac_nonneg (p : ℕ) :
    (0 : ℝ) ≤ (if Nat.Prime p ∧ 2 < p then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1) := by
  split_ifs with h
  · have h3 : (3 : ℝ) ≤ (p : ℝ) := by
      have : 3 ≤ p := by omega
      exact_mod_cast this
    have hden : (1 : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith
    have hle : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 := by
      rw [div_le_one (by nlinarith)]
      exact hden
    linarith
  · norm_num

private lemma twinPartial_fac_le_one (p : ℕ) :
    (if Nat.Prime p ∧ 2 < p then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1) ≤ 1 := by
  split_ifs with h
  · have hpos : (0 : ℝ) ≤ 1 / ((p : ℝ) - 1) ^ 2 := div_nonneg zero_le_one (sq_nonneg _)
    linarith
  · norm_num

private lemma twinPartial_nonneg (Q : ℕ) : (0 : ℝ) ≤ TaoFivePrimes.twinPrimePartial Q := by
  rw [TaoFivePrimes.twinPrimePartial]
  exact Finset.prod_nonneg (fun p _ => twinPartial_fac_nonneg p)

private lemma cast_prod201 :
    ((∏ p ∈ Finset.range 201,
        (if Nat.Prime p ∧ 2 < p then (1 : ℚ) - 1 / ((p : ℚ) - 1) ^ 2 else 1) : ℚ) : ℝ)
      = ∏ p ∈ Finset.range 201,
        (if Nat.Prime p ∧ 2 < p then (1 : ℝ) - 1 / ((p : ℝ) - 1) ^ 2 else 1) := by
  rw [Rat.cast_prod]
  apply Finset.prod_congr rfl
  intro p _
  rw [apply_ite (Rat.cast : ℚ → ℝ)]
  split_ifs <;> push_cast <;> norm_num

private lemma twinPartial_200_ge : (0.66 : ℝ) ≤ TaoFivePrimes.twinPrimePartial 200 := by
  have hQ : (6600 / 10000 : ℚ) ≤
      ∏ p ∈ Finset.range 201,
        (if Nat.Prime p ∧ 2 < p then (1 : ℚ) - 1 / ((p : ℚ) - 1) ^ 2 else 1) := by
    decide +kernel
  have hR : ((6600 / 10000 : ℚ) : ℝ) ≤
      ∏ p ∈ Finset.range 201,
        (if Nat.Prime p ∧ 2 < p then (1 : ℝ) - 1 / ((p : ℝ) - 1) ^ 2 else 1) := by
    have h2 : ((6600 / 10000 : ℚ) : ℝ) ≤
        ((∏ p ∈ Finset.range 201,
          (if Nat.Prime p ∧ 2 < p then (1 : ℚ) - 1 / ((p : ℚ) - 1) ^ 2 else 1) : ℚ) : ℝ) :=
      Rat.cast_le.mpr hQ
    rwa [cast_prod201] at h2
  have hnum : ((6600 / 10000 : ℚ) : ℝ) = (0.66 : ℝ) := by norm_num
  rw [hnum] at hR
  simpa [TaoFivePrimes.twinPrimePartial] using hR

/-- For `Q ≥ 201`, the partial product dominates `partial 200` times the telescoping
coefficient `(200 Q)/(201 (Q-1))`. -/
private lemma twinPartial_ge_200 (Q : ℕ) (hQ : 201 ≤ Q) :
    TaoFivePrimes.twinPrimePartial 200 * (((200 : ℝ) * Q) / (201 * ((Q : ℝ) - 1)))
      ≤ TaoFivePrimes.twinPrimePartial Q := by
  induction Q, hQ using Nat.le_induction with
  | base =>
    have h201 : TaoFivePrimes.twinPrimePartial 201 = TaoFivePrimes.twinPrimePartial 200 := by
      rw [TaoFivePrimes.twinPrimePartial, TaoFivePrimes.twinPrimePartial,
        Finset.prod_range_succ]
      rw [if_neg (show ¬ (Nat.Prime 201 ∧ 2 < 201) by decide), mul_one]
    rw [h201]
    have hcoef : (200 : ℝ) * ((201 : ℕ) : ℝ) / (201 * (((201 : ℕ) : ℝ) - 1)) = 1 := by
      push_cast
      norm_num
    rw [hcoef, mul_one]
  | succ Q hQ ih =>
    have hstep : TaoFivePrimes.twinPrimePartial (Q + 1) =
        TaoFivePrimes.twinPrimePartial Q *
          (if Nat.Prime (Q + 1) ∧ 2 < Q + 1 then
            1 - 1 / (((Q + 1 : ℕ) : ℝ) - 1) ^ 2 else 1) := by
      rw [TaoFivePrimes.twinPrimePartial, TaoFivePrimes.twinPrimePartial,
        Finset.prod_range_succ]
    by_cases hp : Nat.Prime (Q + 1) ∧ 2 < Q + 1
    · rw [hstep, if_pos hp]
      have hfac : (0 : ℝ) ≤ 1 - 1 / (((Q + 1 : ℕ) : ℝ) - 1) ^ 2 := by
        have hsub : (((Q + 1 : ℕ) : ℝ) - 1) = (Q : ℝ) := by push_cast; ring
        rw [hsub]
        have hQ201 : (201 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
        have hden : (1 : ℝ) ≤ (Q : ℝ) ^ 2 := by nlinarith
        have hle : 1 / (Q : ℝ) ^ 2 ≤ 1 := by
          rw [div_le_one (by nlinarith)]
          exact hden
        linarith
      have hkey : TaoFivePrimes.twinPrimePartial 200 *
            ((200 : ℝ) * ((Q + 1 : ℕ) : ℝ) / (201 * (((Q + 1 : ℕ) : ℝ) - 1)))
          = (TaoFivePrimes.twinPrimePartial 200 * (((200 : ℝ) * Q) / (201 * ((Q : ℝ) - 1)))) *
            (1 - 1 / (((Q + 1 : ℕ) : ℝ) - 1) ^ 2) := by
        have hQ1 : (1 : ℝ) < (Q : ℝ) := by exact_mod_cast (by omega : 1 < Q)
        have hQ1' : (0 : ℝ) < (Q : ℝ) - 1 := by linarith
        have hQ0 : (0 : ℝ) < (Q : ℝ) := by linarith
        have hQne : (Q : ℝ) ≠ 0 := ne_of_gt hQ0
        have hQ1ne : (Q : ℝ) - 1 ≠ 0 := ne_of_gt hQ1'
        push_cast
        simp only [add_sub_cancel_right]
        field_simp
        ring
      rw [hkey]
      exact mul_le_mul_of_nonneg_right ih hfac
    · rw [hstep, if_neg hp, mul_one]
      refine le_trans ?_ ih
      have hcoef : (200 : ℝ) * ((Q + 1 : ℕ) : ℝ) / (201 * (((Q + 1 : ℕ) : ℝ) - 1))
          ≤ (200 : ℝ) * Q / (201 * ((Q : ℝ) - 1)) := by
        have hQ1 : (1 : ℝ) < (Q : ℝ) := by exact_mod_cast (by omega : 1 < Q)
        have hQ1' : (0 : ℝ) < (Q : ℝ) - 1 := by linarith
        have hQ0 : (0 : ℝ) < (Q : ℝ) := by linarith
        push_cast
        rw [div_le_div_iff₀ (by nlinarith) (by nlinarith)]
        nlinarith
      exact mul_le_mul_of_nonneg_left hcoef (twinPartial_nonneg 200)

private lemma twinPartial_ge_655 (Q : ℕ) : (0.655 : ℝ) ≤ TaoFivePrimes.twinPrimePartial Q := by
  rcases le_or_gt Q 200 with hQ | hQ
  · have hle : TaoFivePrimes.twinPrimePartial 200 ≤ TaoFivePrimes.twinPrimePartial Q := by
      rw [TaoFivePrimes.twinPrimePartial, TaoFivePrimes.twinPrimePartial]
      refine Finset.prod_le_prod_of_subset_of_le_one (s := Finset.range (Q + 1))
        (t := Finset.range 201)
        (f := fun p => if Nat.Prime p ∧ 2 < p then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1)
        ?_ ?_ ?_
      · intro i hi
        simp only [Finset.mem_range] at hi ⊢
        omega
      · intro i _
        exact twinPartial_fac_nonneg i
      · intro i _ _
        exact twinPartial_fac_le_one i
    linarith [twinPartial_200_ge]
  · have hbig := twinPartial_ge_200 Q hQ
    have hcoef : (200 : ℝ) / 201 ≤ ((200 : ℝ) * Q) / (201 * ((Q : ℝ) - 1)) := by
      have hQ1 : (1 : ℝ) < (Q : ℝ) := by exact_mod_cast (by omega : 1 < Q)
      have hQ1' : (0 : ℝ) < (Q : ℝ) - 1 := by linarith
      rw [div_le_div_iff₀ (by norm_num) (by nlinarith)]
      nlinarith
    have h1 : TaoFivePrimes.twinPrimePartial 200 * ((200 : ℝ) / 201)
        ≤ TaoFivePrimes.twinPrimePartial Q :=
      le_trans (mul_le_mul_of_nonneg_left hcoef (twinPartial_nonneg 200)) hbig
    have h2 : (0.655 : ℝ) ≤ TaoFivePrimes.twinPrimePartial 200 * ((200 : ℝ) / 201) := by
      have h3 := mul_le_mul_of_nonneg_right twinPartial_200_ge
        (by norm_num : (0 : ℝ) ≤ (200 : ℝ) / 201)
      linarith [h3]
    linarith

end ReciprocalSharperConstant

theorem solution : (131/100 : ℝ) ≤ TaoFivePrimes.twinPrimeConstant := by
  unfold TaoFivePrimes.twinPrimeConstant
  have hne : (Set.range TaoFivePrimes.twinPrimePartial).Nonempty := ⟨_, 0, rfl⟩
  have hsInf : (0.655 : ℝ) ≤ sInf (Set.range TaoFivePrimes.twinPrimePartial) :=
    le_csInf hne (by rintro _ ⟨Q, rfl⟩; exact ReciprocalSharperConstant.twinPartial_ge_655 Q)
  linarith

example : (131/100 : ℝ) ≤ TaoFivePrimes.twinPrimeConstant := solution
#print axioms solution
