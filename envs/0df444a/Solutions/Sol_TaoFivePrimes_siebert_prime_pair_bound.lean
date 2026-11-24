-- Prove2me | solution 1 for TaoFivePrimes.siebert_prime_pair_bound
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-23T13:44:37.743925+00:00
-- url     : https://prove2.me/submissions/f519ace2-8180-4257-bee3-5f2267eb863d

import Theorems.Thm_PrimePairSieve_prime_pair_count_base_reciprocal_bound
import Theorems.Thm_PrimePairSieve_reciprocal_base_denominator_dominates_threshold
import Theorems.Thm_PrimePairSieve_prime_pair_count_base_finite_range
import Definitions.Def_TaoFivePrimes_SingularSeries
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Convert
import Lean.Elab.Tactic.Omega

open scoped BigOperators

namespace TaoFivePrimes

private noncomputable def sicFullPartial (Q : ℕ) : ℝ :=
  ∏ p ∈ Finset.range (Q + 1), if 2 < p then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1

private theorem sicFullPartial_formula (n : ℕ) :
    sicFullPartial (n + 2) = ((n : ℝ) + 2) / (2 * ((n : ℝ) + 1)) := by
  induction n with
  | zero => norm_num [sicFullPartial, Finset.prod_range_succ]
  | succ n ih =>
    have hrec : sicFullPartial (n + 1 + 2) =
        sicFullPartial (n + 2) * (1 - 1 / (((n + 3 : ℕ) : ℝ) - 1) ^ 2) := by
      unfold sicFullPartial
      rw [show n + 1 + 2 + 1 = (n + 2 + 1) + 1 by omega, Finset.prod_range_succ]
      simp [show 2 < n + 2 + 1 by omega]
    rw [hrec, ih]
    push_cast
    have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
    convert_to
      (((n : ℝ) + 2) / (2 * ((n : ℝ) + 1))) *
          (1 - 1 / ((n : ℝ) + 2) ^ 2) =
        ((n : ℝ) + 3) / (2 * ((n : ℝ) + 2)) using 1 <;> try ring
    field_simp
    <;> ring

private theorem sicFactor_nonneg (p : ℕ) (hp : 2 < p) :
    0 ≤ (1 : ℝ) - 1 / ((p : ℝ) - 1) ^ 2 := by
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hsq : 1 ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith
  exact sub_nonneg.mpr ((div_le_one (by linarith : (0 : ℝ) < ((p : ℝ) - 1) ^ 2)).mpr hsq)

private theorem sicFullPartial_le (Q : ℕ) : sicFullPartial Q ≤ twinPrimePartial Q := by
  unfold sicFullPartial twinPrimePartial
  apply Finset.prod_le_prod
  · intro p hp
    split_ifs with h
    · exact sicFactor_nonneg p h
    · norm_num
  · intro p hp
    by_cases h : 2 < p
    · by_cases hprime : Nat.Prime p
      · simp [h, hprime]
      · simp only [h, hprime, false_and, if_false, if_true]
        exact sub_le_self _ (by positivity)
    · simp [h]

private theorem sicTwinPrimePartial_bounds (Q : ℕ) :
    (1 / 2 : ℝ) ≤ twinPrimePartial Q ∧ twinPrimePartial Q ≤ 1 := by
  constructor
  · have hfull : (1 / 2 : ℝ) ≤ sicFullPartial Q := by
      rcases Q with _ | _ | n
      · norm_num [sicFullPartial]
      · norm_num [sicFullPartial, Finset.prod_range_succ]
      · change (1 / 2 : ℝ) ≤ sicFullPartial (n + 2)
        rw [sicFullPartial_formula]
        apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * ((n : ℝ) + 1))).mpr
        linarith
    exact hfull.trans (sicFullPartial_le Q)
  · unfold twinPrimePartial
    apply Finset.prod_le_one
    · intro p hp
      split_ifs with h
      · exact sicFactor_nonneg p h.2
      · norm_num
    · intro p hp
      split_ifs
      · exact sub_le_self _ (by positivity)
      · exact le_rfl

private theorem siebert_twinPrimeConstant_bounds :
    1 ≤ twinPrimeConstant ∧ twinPrimeConstant ≤ 3 / 2 := by
  have hn : (Set.range twinPrimePartial).Nonempty := Set.range_nonempty _
  have hb : BddBelow (Set.range twinPrimePartial) :=
    ⟨1 / 2, by rintro _ ⟨Q, rfl⟩; exact (sicTwinPrimePartial_bounds Q).1⟩
  have hlo : (1 / 2 : ℝ) ≤ sInf (Set.range twinPrimePartial) := by
    apply le_csInf hn
    rintro _ ⟨Q, rfl⟩
    exact (sicTwinPrimePartial_bounds Q).1
  have hhi : sInf (Set.range twinPrimePartial) ≤ twinPrimePartial 3 :=
    csInf_le hb (Set.mem_range_self _)
  have hthree : twinPrimePartial 3 = 3 / 4 := by
    norm_num [twinPrimePartial, Finset.prod_range_succ, Nat.prime_three]
  rw [hthree] at hhi
  unfold twinPrimeConstant
  constructor <;> linarith

private lemma endgame_arith
    {C x z K Bz T s : ℝ}
    (hC : 0 < C) (hC1 : 1 ≤ C) (hz1 : 1 < z)
    (hxe : x = 16 * z ^ 2)
    (hlogx : Real.log x = 2 * Real.log (4 * z))
    (hT : T = (Real.log (4 * z)) ^ 2 / (2 * C))
    (hs : s = (z + 1) * T / (16 * z ^ 2))
    (hlogb : (Real.log (4 * z)) ^ 2 ≤ 16 * z)
    (hK : 1 ≤ K)
    (hBz : T / (1 - s) ≤ Bz) :
    K * x / Bz + z + 1 ≤ 8 * C * K * x / (Real.log x) ^ 2 := by
  have hz0 : 0 < z := by linarith
  have h4z1 : 1 < 4 * z := by linarith
  have hlog4pos : 0 < Real.log (4 * z) := Real.log_pos h4z1
  have hlog4ne : Real.log (4 * z) ≠ 0 := ne_of_gt hlog4pos
  have hTpos : 0 < T := by rw [hT]; positivity
  have hslt : s < 1 := by
    have h1 : s ≤ (z + 1) / (2 * z) := by
      rw [hs, hT, div_le_iff₀ (by positivity : (0 : ℝ) < 16 * z ^ 2)]
      have hmid : (Real.log (4 * z)) ^ 2 / (2 * C) ≤ 8 * z := by
        have ha : 0 ≤ (Real.log (4 * z)) ^ 2 := sq_nonneg _
        have h1 : (Real.log (4 * z)) ^ 2 / (2 * C) ≤ (Real.log (4 * z)) ^ 2 / 2 :=
          div_le_div_of_nonneg_left ha (by norm_num) (by linarith)
        have h2 : (Real.log (4 * z)) ^ 2 / 2 ≤ 16 * z / 2 :=
          div_le_div_of_nonneg_right hlogb (by norm_num)
        linarith
      have h3 : (z + 1) / (2 * z) * (16 * z ^ 2) = (z + 1) * (8 * z) := by
        field_simp
        ring
      rw [h3]
      exact mul_le_mul_of_nonneg_left hmid (by linarith)
    have h2 : (z + 1) / (2 * z) < 1 := by
      rw [div_lt_one (by positivity : (0 : ℝ) < 2 * z)]
      linarith
    linarith
  have h1s : 0 < 1 - s := by linarith
  have hTreqpos : 0 < T / (1 - s) := div_pos hTpos h1s
  have hx0 : 0 < x := by rw [hxe]; positivity
  have hlogxne : Real.log x ≠ 0 := by
    rw [hlogx]
    exact mul_ne_zero two_ne_zero hlog4ne
  have hKx0 : 0 ≤ K * x := by nlinarith [hK, hx0]
  have step1 : K * x / Bz ≤ K * x / (T / (1 - s)) :=
    div_le_div_of_nonneg_left hKx0 hTreqpos hBz
  have step2 : K * x / (T / (1 - s)) = K * x * (1 - s) / T := by
    rw [div_div_eq_mul_div]
  have hsx : x * s / T = z + 1 := by
    rw [hs, hxe]
    field_simp [ne_of_gt hTpos]
  have step3 : K * x * (1 - s) / T = K * x / T - K * (z + 1) := by
    have hxs : x * (1 - s) / T = x / T - (z + 1) := by
      rw [mul_sub, sub_div, hsx]
      ring
    calc K * x * (1 - s) / T = K * (x * (1 - s) / T) := by ring
      _ = K * (x / T - (z + 1)) := by rw [hxs]
      _ = K * x / T - K * (z + 1) := by ring
  have step4 : K * x / T - K * (z + 1) + z + 1 ≤ K * x / T := by
    have hKz : z + 1 ≤ K * (z + 1) := by nlinarith [hK, hz0]
    linarith
  have step5 : K * x / T = 8 * C * K * x / (Real.log x) ^ 2 := by
    rw [hT, hlogx]
    have hL2 : (Real.log (4 * z)) ^ 2 ≠ 0 := pow_ne_zero 2 hlog4ne
    rw [div_div_eq_mul_div]
    rw [show (2 * Real.log (4 * z)) ^ 2 = 4 * (Real.log (4 * z)) ^ 2 by ring]
    rw [div_eq_div_iff hL2 (mul_ne_zero (by norm_num) hL2)]
    ring
  calc K * x / Bz + z + 1
      ≤ K * x / (T / (1 - s)) + z + 1 := by linarith [step1]
    _ = K * x * (1 - s) / T + z + 1 := by rw [step2]
    _ = K * x / T - K * (z + 1) + z + 1 := by rw [step3]
    _ ≤ K * x / T := step4
    _ = 8 * C * K * x / (Real.log x) ^ 2 := step5

theorem siebert_prime_pair_bound (x d : ℕ) (hx : 2 ≤ x) (hd0 : 0 < d)
    (hd2 : 2 ∣ d) :
    (∑ n ∈ Finset.range (x + 1),
      if Nat.Prime n ∧ Nat.Prime (n + d) ∧ n + d ≤ x then (1 : ℝ) else 0) ≤
      8 * twinPrimeConstant * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 *
        ∏ p ∈ Nat.primeFactors d, if 2 < p then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1 := by
  by_cases hX : x ≤ 25600
  · exact PrimePairSieve.prime_pair_count_base_finite_range x d hx hX hd0 hd2
  · have hX25600 : 25600 < x := by omega
    have hx16 : 16 ≤ x := by omega
    obtain ⟨z, hzdef⟩ : ∃ z : ℝ, z = Real.sqrt (x : ℝ) / 4 := ⟨_, rfl⟩
    set K : ℝ := ∏ p ∈ Nat.primeFactors d,
      if 2 < p then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1 with hKdef
    obtain ⟨Bz, hBzdef⟩ : ∃ Bz : ℝ, Bz = ∑ q ∈ Finset.Icc 1 ⌊z⌋₊,
        (if Squarefree q then ∏ p ∈ q.primeFactors,
          if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2) else 0) /
            (1 + (q : ℝ) / z) := ⟨_, rfl⟩
    have hbd := PrimePairSieve_prime_pair_count_base_reciprocal_bound x d hx16 hd0 hd2
    rw [← hzdef] at hbd
    rw [← hKdef] at hbd
    rw [← hBzdef] at hbd
    have hCpos : 0 < twinPrimeConstant :=
      lt_of_lt_of_le zero_lt_one siebert_twinPrimeConstant_bounds.1
    have hC1 : (1 : ℝ) ≤ twinPrimeConstant := siebert_twinPrimeConstant_bounds.1
    have hz40 : 40 ≤ z := by
      rw [hzdef]
      have h160 : (160 : ℝ) < Real.sqrt (x : ℝ) := by
        rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 160)]
        exact_mod_cast (by omega : 160 ^ 2 < x)
      linarith
    have hz1 : 1 < z := by linarith
    have hz0 : 0 < z := by linarith
    have hxe : (x : ℝ) = 16 * z ^ 2 := by
      rw [hzdef, div_pow, Real.sq_sqrt (Nat.cast_nonneg x)]
      ring
    have hlogx : Real.log (x : ℝ) = 2 * Real.log (4 * z) := by
      calc Real.log (x : ℝ) = Real.log (16 * z ^ 2) := by rw [hxe]
        _ = Real.log 16 + Real.log (z ^ 2) :=
            Real.log_mul (by norm_num) (pow_ne_zero 2 (ne_of_gt hz0))
        _ = 4 * Real.log 2 + 2 * Real.log z := by
            rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow, Real.log_pow]
            push_cast
            ring
        _ = 2 * (Real.log 4 + Real.log z) := by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
            ring
        _ = 2 * Real.log (4 * z) := by
            rw [Real.log_mul (by norm_num) (ne_of_gt hz0)]
    have hlogb : (Real.log (4 * z)) ^ 2 ≤ 16 * z := by
      have hsqrt4z : 0 < Real.sqrt (4 * z) := Real.sqrt_pos.mpr (by linarith)
      have h1 : Real.log (Real.sqrt (4 * z)) ≤ Real.sqrt (4 * z) - 1 :=
        Real.log_le_sub_one_of_pos hsqrt4z
      have h2 : Real.log (Real.sqrt (4 * z)) = Real.log (4 * z) / 2 :=
        Real.log_sqrt (by linarith)
      have h3 : Real.log (4 * z) ≤ 2 * Real.sqrt (4 * z) - 2 := by linarith
      have h4 : Real.sqrt (4 * z) = 2 * Real.sqrt z := by
        rw [show (4 : ℝ) * z = 2 ^ 2 * z by ring,
          Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2 ^ 2), Real.sqrt_sq (by norm_num)]
      have h3' : Real.log (4 * z) ≤ 4 * Real.sqrt z - 2 := by
        rw [h4] at h3
        linarith
      have h5 : 0 ≤ Real.log (4 * z) := le_of_lt (Real.log_pos (by linarith))
      have h6 : 0 ≤ 4 * Real.sqrt z - 2 := by
        have hs : (Real.sqrt z) ^ 2 = z := Real.sq_sqrt (by linarith)
        have : (1 : ℝ) ≤ Real.sqrt z := by nlinarith [Real.sqrt_nonneg z]
        linarith
      have h7 : (Real.log (4 * z)) ^ 2 ≤ (4 * Real.sqrt z - 2) ^ 2 :=
        sq_le_sq' (by linarith) h3'
      have h8 : (4 * Real.sqrt z - 2) ^ 2 ≤ 16 * z := by
        have hs : (Real.sqrt z) ^ 2 = z := Real.sq_sqrt (by linarith)
        have hs1 : (1 : ℝ) ≤ Real.sqrt z := by nlinarith [Real.sqrt_nonneg z]
        nlinarith
      linarith
    have hK1 : 1 ≤ K := by
      rw [hKdef]
      apply Finset.one_le_prod
      intro p hp
      by_cases h2p : 2 < p
      · simp only [h2p, if_true]
        have hp2 : (2 : ℝ) < (p : ℝ) := by exact_mod_cast h2p
        rw [one_le_div (by linarith : (0 : ℝ) < (p : ℝ) - 2)]
        linarith
      · simp [h2p]
    have hD := PrimePairSieve.reciprocal_base_denominator_dominates_threshold z hz40
    rw [← hBzdef] at hD
    have hE := endgame_arith (C := twinPrimeConstant) (x := (x : ℝ)) (z := z)
      (K := K) (Bz := Bz)
      (T := (Real.log (4 * z)) ^ 2 / (2 * twinPrimeConstant))
      (s := (z + 1) * ((Real.log (4 * z)) ^ 2 / (2 * twinPrimeConstant)) / (16 * z ^ 2))
      hCpos hC1 hz1 hxe hlogx rfl rfl hlogb hK1 hD
    refine le_trans hbd ?_
    calc K * (x : ℝ) / Bz + z + 1
        ≤ 8 * twinPrimeConstant * K * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 := hE
      _ = 8 * twinPrimeConstant * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 * K := by ring

end TaoFivePrimes

theorem solution (x d : ℕ) (hx : 2 ≤ x) (hd0 : 0 < d) (hd2 : 2 ∣ d) :
    (∑ n ∈ Finset.range (x + 1),
      if Nat.Prime n ∧ Nat.Prime (n + d) ∧ n + d ≤ x then (1 : ℝ) else 0) ≤
      8 * TaoFivePrimes.twinPrimeConstant * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 *
        ∏ p ∈ Nat.primeFactors d, if 2 < p then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1 :=
  TaoFivePrimes.siebert_prime_pair_bound x d hx hd0 hd2
