-- Prove2me | solution 1 for brun_theorem
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-27T03:30:11.043179+00:00
-- url     : https://prove2.me/submissions/a9ebfc60-8e66-4a93-8df1-2339cad075b8

import Mathlib
import Theorems.Thm_PrimePairSieve_prime_pair_count_base_reciprocal_bound
import Theorems.Thm_PrimePairSieve_reciprocal_base_denominator_dominates_threshold
import Theorems.Thm_PrimePairSieve_twin_prime_constant_lower_131
import Definitions.Def_TaoFivePrimes_SingularSeries

open scoped BigOperators

set_option autoImplicit false

/- Brun's theorem (unconditional): the sum of reciprocals of twin primes
   converges. Analysis half via dyadic blocks (draft), count bound M1 via
   the PrimePairSieve theorems (pair-count bound, threshold bound, and the
   1.31 lower bound for the twin-prime constant). -/

noncomputable def twinInd (n : ℕ) : ℝ :=
  if Nat.Prime n ∧ Nat.Prime (n + 2) then (n : ℝ)⁻¹ else 0

lemma twinInd_nonneg (n : ℕ) : 0 ≤ twinInd n := by
  unfold twinInd
  split_ifs with h
  · positivity
  · exact le_refl 0

lemma twinInd_le_one (n : ℕ) : twinInd n ≤ 1 := by
  unfold twinInd
  split_ifs with h
  · exact inv_le_one_of_one_le₀ (by exact_mod_cast h.1.one_lt.le)
  · exact zero_le_one

/-- Dyadic block decomposition of an initial segment `range (2^K + 1)`. -/
lemma sum_range_pow_two_add_one (f : ℕ → ℝ) :
    ∀ K : ℕ, ∑ i ∈ Finset.range (2 ^ K + 1), f i
      = f 0 + f 1
        + ∑ k ∈ Finset.range K, ∑ i ∈ Finset.Ioc (2 ^ k) (2 ^ (k + 1)), f i := by
  intro K
  induction K with
  | zero => simp [Finset.sum_range_succ]
  | succ K ih =>
    have hpow : 2 ^ K ≤ 2 ^ (K + 1) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.le_succ K)
    have hIco : Finset.Ico (2 ^ K + 1) (2 ^ (K + 1) + 1)
        = Finset.Ioc (2 ^ K) (2 ^ (K + 1)) := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_Ioc]
      omega
    have hsplit : ∑ i ∈ Finset.Ico 0 (2 ^ (K + 1) + 1), f i
        = ∑ i ∈ Finset.Ico 0 (2 ^ K + 1), f i
          + ∑ i ∈ Finset.Ico (2 ^ K + 1) (2 ^ (K + 1) + 1), f i :=
      (Finset.sum_Ico_consecutive f (Nat.zero_le _)
        (Nat.add_le_add_right hpow 1)).symm
    calc ∑ i ∈ Finset.range (2 ^ (K + 1) + 1), f i
        = ∑ i ∈ Finset.Ico 0 (2 ^ (K + 1) + 1), f i := by
          rw [Finset.range_eq_Ico]
      _ = ∑ i ∈ Finset.Ico 0 (2 ^ K + 1), f i
          + ∑ i ∈ Finset.Ico (2 ^ K + 1) (2 ^ (K + 1) + 1), f i := hsplit
      _ = ∑ i ∈ Finset.range (2 ^ K + 1), f i
          + ∑ i ∈ Finset.Ioc (2 ^ K) (2 ^ (K + 1)), f i := by
          rw [← Finset.range_eq_Ico, hIco]
      _ = (f 0 + f 1
          + ∑ k ∈ Finset.range K, ∑ i ∈ Finset.Ioc (2 ^ k) (2 ^ (k + 1)), f i)
          + ∑ i ∈ Finset.Ioc (2 ^ K) (2 ^ (K + 1)), f i := by rw [ih]
      _ = f 0 + f 1
          + ∑ k ∈ Finset.range (K + 1),
            ∑ i ∈ Finset.Ioc (2 ^ k) (2 ^ (k + 1)), f i := by
          rw [Finset.sum_range_succ]; ring

/-- One dyadic block, bounded by the twin-count hypothesis. -/
lemma block_sum_le (C : ℝ) (_hC : 0 ≤ C)
    (hcount : ∀ k : ℕ,
      (((Finset.Ioc (2 ^ k) (2 ^ (k + 1))).filter
        (fun n => Nat.Prime n ∧ Nat.Prime (n + 2))).card : ℝ)
        ≤ C * (2 : ℝ) ^ k / ((k : ℝ) + 1) ^ 2)
    (k : ℕ) :
    ∑ i ∈ Finset.Ioc (2 ^ k) (2 ^ (k + 1)), twinInd i
      ≤ C / ((k : ℝ) + 1) ^ 2 := by
  classical
  have h2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have h2k0 : (2 : ℝ) ^ k ≠ 0 := ne_of_gt h2k
  have hstep1 : ∑ i ∈ Finset.Ioc (2 ^ k) (2 ^ (k + 1)), twinInd i
      = ∑ i ∈ (Finset.Ioc (2 ^ k) (2 ^ (k + 1))).filter
          (fun n => Nat.Prime n ∧ Nat.Prime (n + 2)), (i : ℝ)⁻¹ := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    rfl
  rw [hstep1]
  calc ∑ i ∈ (Finset.Ioc (2 ^ k) (2 ^ (k + 1))).filter
          (fun n => Nat.Prime n ∧ Nat.Prime (n + 2)), (i : ℝ)⁻¹
      ≤ ((Finset.Ioc (2 ^ k) (2 ^ (k + 1))).filter
          (fun n => Nat.Prime n ∧ Nat.Prime (n + 2))).card • ((2 : ℝ) ^ k)⁻¹ :=
        Finset.sum_le_card_nsmul _ _ _ (fun i hi => by
          have hiIoc := (Finset.mem_filter.mp hi).1
          have hlt : (2 : ℝ) ^ k < (i : ℝ) := by
            exact_mod_cast (Finset.mem_Ioc.mp hiIoc).1
          simpa only [inv_eq_one_div] using
            one_div_le_one_div_of_le h2k hlt.le)
    _ = ((Finset.Ioc (2 ^ k) (2 ^ (k + 1))).filter
          (fun n => Nat.Prime n ∧ Nat.Prime (n + 2))).card • ((2 : ℝ) ^ k)⁻¹ := rfl
    _ = (((Finset.Ioc (2 ^ k) (2 ^ (k + 1))).filter
          (fun n => Nat.Prime n ∧ Nat.Prime (n + 2))).card : ℝ)
          * ((2 : ℝ) ^ k)⁻¹ := by rw [nsmul_eq_mul]
    _ ≤ (C * (2 : ℝ) ^ k / ((k : ℝ) + 1) ^ 2) * ((2 : ℝ) ^ k)⁻¹ :=
        mul_le_mul_of_nonneg_right (hcount k) (inv_nonneg.mpr h2k.le)
    _ = C / ((k : ℝ) + 1) ^ 2 * ((2 : ℝ) ^ k * ((2 : ℝ) ^ k)⁻¹) := by ring
    _ = C / ((k : ℝ) + 1) ^ 2 := by rw [mul_inv_cancel₀ h2k0, mul_one]

/-- The analysis half of Brun's theorem, over ℕ (conditional on the count bound). -/
theorem brun_summable_of_count_bound
    (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ k : ℕ,
      (((Finset.Ioc (2 ^ k) (2 ^ (k + 1))).filter
        (fun n => Nat.Prime n ∧ Nat.Prime (n + 2))).card : ℝ)
        ≤ C * (2 : ℝ) ^ k / ((k : ℝ) + 1) ^ 2) :
    Summable twinInd := by
  have hsum1 : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hsum2 : Summable (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1) ^ 2) := by
    have h := (summable_nat_add_iff
      (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).mpr hsum1
    refine h.congr (fun k => ?_)
    simp only [Nat.cast_add, Nat.cast_one]
  have hsumC : Summable (fun k : ℕ => C / ((k : ℝ) + 1) ^ 2) := by
    have h := hsum2.mul_left C
    refine h.congr (fun k => ?_)
    rw [mul_one_div]
  apply summable_of_sum_range_le (fun n => twinInd_nonneg n)
  intro n
  obtain ⟨K, hK⟩ : ∃ K, n < 2 ^ K :=
    ⟨(Nat.log 2 n).succ, Nat.lt_pow_succ_log_self (by norm_num) n⟩
  have hsub : Finset.range n ⊆ Finset.range (2 ^ K + 1) := by
    intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  have hle1 : ∑ i ∈ Finset.range n, twinInd i
      ≤ ∑ i ∈ Finset.range (2 ^ K + 1), twinInd i :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => twinInd_nonneg i)
  rw [sum_range_pow_two_add_one twinInd K] at hle1
  have hblocks : ∑ k ∈ Finset.range K,
      ∑ i ∈ Finset.Ioc (2 ^ k) (2 ^ (k + 1)), twinInd i
      ≤ ∑' k : ℕ, C / ((k : ℝ) + 1) ^ 2 := by
    calc ∑ k ∈ Finset.range K,
          ∑ i ∈ Finset.Ioc (2 ^ k) (2 ^ (k + 1)), twinInd i
        ≤ ∑ k ∈ Finset.range K, C / ((k : ℝ) + 1) ^ 2 :=
          Finset.sum_le_sum (fun k _ => block_sum_le C hC hcount k)
      _ ≤ ∑' k : ℕ, C / ((k : ℝ) + 1) ^ 2 :=
          hsumC.sum_le_tsum (Finset.range K)
            (fun i _ => div_nonneg hC (by positivity))
  calc ∑ i ∈ Finset.range n, twinInd i
      ≤ twinInd 0 + twinInd 1
        + ∑ k ∈ Finset.range K,
          ∑ i ∈ Finset.Ioc (2 ^ k) (2 ^ (k + 1)), twinInd i := hle1
    _ ≤ 2 + ∑' k : ℕ, C / ((k : ℝ) + 1) ^ 2 := by
        have h01 : twinInd 0 + twinInd 1 ≤ 2 := by
          have h0 := twinInd_le_one 0
          have h1 := twinInd_le_one 1
          linarith
        linarith

/-- The conditional theorem in platform-style subtype form. -/
theorem brun_theorem_of_count_bound
    (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ k : ℕ,
      (((Finset.Ioc (2 ^ k) (2 ^ (k + 1))).filter
        (fun n => Nat.Prime n ∧ Nat.Prime (n + 2))).card : ℝ)
        ≤ C * (2 : ℝ) ^ k / ((k : ℝ) + 1) ^ 2) :
    Summable (fun p : {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2)} => (p : ℝ)⁻¹) := by
  have h : Summable (twinInd ∘
      (Subtype.val : {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2)} → ℕ)) :=
    (brun_summable_of_count_bound C hC hcount).comp_injective Subtype.val_injective
  refine h.congr (fun p => ?_)
  show twinInd p.val = (p.val : ℝ)⁻¹
  unfold twinInd
  split_ifs with hcond
  · rfl
  · exact absurd p.2 hcond

lemma aux_bounds (j : ℕ) :
    ((15 : ℝ) + j) ^ 2 ≤ (21 / 2) * (2 : ℝ) ^ (14 + j) ∧
    ((15 : ℝ) + j) ^ 4 ≤ 245000 * (2 : ℝ) ^ (14 + j) := by
  induction j with
  | zero => constructor <;> norm_num
  | succ j ih =>
    obtain ⟨ih2, ih4⟩ := ih
    have hstep : (16 : ℝ) + j ≤ (16 / 15) * ((15 : ℝ) + j) := by
      have h2 : (1 : ℝ) ≤ ((15 : ℝ) + j) / 15 := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 15)]
        simp only [one_mul]
        have h15 : (15 : ℝ) ≤ (15 : ℝ) + j := by
          have := Nat.cast_nonneg (α := ℝ) j
          linarith
        linarith
      calc (16 : ℝ) + j = ((15 : ℝ) + j) + 1 := by ring
        _ ≤ ((15 : ℝ) + j) + ((15 : ℝ) + j) / 15 := by linarith
        _ = (16 / 15) * ((15 : ℝ) + j) := by field_simp; ring
    have e2 : (15 : ℝ) + ((j + 1 : ℕ) : ℝ) = (16 : ℝ) + j := by push_cast; ring
    have e4 : (14 + (j + 1) : ℕ) = (14 + j) + 1 := by omega
    rw [e2, e4, pow_succ]
    constructor
    · calc ((16 : ℝ) + j) ^ 2
          ≤ ((16 / 15) * ((15 : ℝ) + j)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) hstep 2
        _ = (16 / 15) ^ 2 * ((15 : ℝ) + j) ^ 2 := by rw [mul_pow]
        _ ≤ 2 * ((15 : ℝ) + j) ^ 2 := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            norm_num
        _ ≤ 2 * ((21 / 2) * (2 : ℝ) ^ (14 + j)) := by
            apply mul_le_mul_of_nonneg_left ih2 (by norm_num)
        _ = (21 / 2) * ((2 : ℝ) ^ (14 + j) * 2) := by ring
    · calc ((16 : ℝ) + j) ^ 4
          ≤ ((16 / 15) * ((15 : ℝ) + j)) ^ 4 :=
            pow_le_pow_left₀ (by positivity) hstep 4
        _ = (16 / 15) ^ 4 * ((15 : ℝ) + j) ^ 4 := by rw [mul_pow]
        _ ≤ 2 * ((15 : ℝ) + j) ^ 4 := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            norm_num
        _ ≤ 2 * (245000 * (2 : ℝ) ^ (14 + j)) := by
            apply mul_le_mul_of_nonneg_left ih4 (by norm_num)
        _ = 245000 * ((2 : ℝ) ^ (14 + j) * 2) := by ring

/-- The threshold consequence, isolated with short variable names: the sifted
    sum D is at least (log (4z))² / (2·C₂), once the error term err is shown
    to be < 1 (so that L ≤ L / (1 - err) ≤ D). -/
lemma denom_lower (z C₂ Dsum : ℝ) (hz : 40 ≤ z) (hC₂ : (131 / 100 : ℝ) ≤ C₂)
    (hthr : (Real.log (4 * z)) ^ 2 / (2 * C₂) /
      (1 - (z + 1) * ((Real.log (4 * z)) ^ 2 / (2 * C₂)) / (16 * z ^ 2)) ≤ Dsum) :
    (Real.log (4 * z)) ^ 2 / (2 * C₂) ≤ Dsum := by
  have hzpos : (0 : ℝ) < z := by linarith
  have hC₂pos : (0 : ℝ) < C₂ := by linarith
  have hC₂ne : C₂ ≠ 0 := ne_of_gt hC₂pos
  have h4zpos : (0 : ℝ) < 4 * z := by linarith
  have hlog_pos : (0 : ℝ) < Real.log (4 * z) :=
    Real.log_pos (by linarith : (1 : ℝ) < 4 * z)
  have hlog_nn : (0 : ℝ) ≤ Real.log (4 * z) := le_of_lt hlog_pos
  -- log(4z) < 4√z, from log t < 2√t (via log √t < √t).
  have hlog_lt : Real.log (4 * z) < 4 * Real.sqrt z := by
    have hh1 : Real.log (4 * z) = 2 * Real.log (Real.sqrt (4 * z)) := by
      rw [Real.log_sqrt (by linarith : (0 : ℝ) ≤ 4 * z)]; ring
    have hh2 : Real.log (Real.sqrt (4 * z)) < Real.sqrt (4 * z) := by
      have hh := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr h4zpos)
      linarith
    have hh3 : Real.sqrt (4 * z) = 2 * Real.sqrt z := by
      rw [show (4 : ℝ) * z = 2 ^ 2 * z by ring,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2 ^ 2),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  -- Squaring: (log(4z))² < 16z.
  have hlog_sq : (Real.log (4 * z)) ^ 2 < 16 * z := by
    have hsq : (Real.sqrt z) ^ 2 = z := Real.sq_sqrt (le_of_lt hzpos)
    have hprod : (0 : ℝ) < (4 * Real.sqrt z - Real.log (4 * z)) *
        (4 * Real.sqrt z + Real.log (4 * z)) := by
      apply mul_pos (by linarith) (by have := Real.sqrt_pos.mpr hzpos; linarith)
    nlinarith [hprod, hsq]
  -- The error term is < 1.
  have herr : (z + 1) * ((Real.log (4 * z)) ^ 2 / (2 * C₂)) / (16 * z ^ 2) < 1 := by
    rw [div_lt_one (mul_pos (by norm_num : (0 : ℝ) < 16) (pow_pos hzpos 2))]
    calc (z + 1) * ((Real.log (4 * z)) ^ 2 / (2 * C₂))
        < (z + 1) * (16 * z / (2 * C₂)) := by
          apply mul_lt_mul_of_pos_left _ (by linarith)
          have h2C₂ : (0 : ℝ) < 2 * C₂ := by linarith
          rw [show (16 * z / (2 * C₂)) = (16 * z) * (2 * C₂)⁻¹ by rw [div_eq_mul_inv],
              show ((Real.log (4 * z)) ^ 2 / (2 * C₂)) =
                ((Real.log (4 * z)) ^ 2) * (2 * C₂)⁻¹ by rw [div_eq_mul_inv]]
          exact mul_lt_mul_of_pos_right hlog_sq (inv_pos.mpr h2C₂)
      _ = (z + 1) * 8 * z / C₂ := by field_simp; ring
      _ ≤ 16 * z ^ 2 / C₂ := by
          have hle : (z + 1) * 8 * z ≤ 16 * z ^ 2 := by
            nlinarith [mul_nonneg (show (0 : ℝ) ≤ z - 1 by linarith) (le_of_lt hzpos)]
          calc (z + 1) * 8 * z / C₂ = ((z + 1) * 8 * z) * C₂⁻¹ := by rw [div_eq_mul_inv]
            _ ≤ (16 * z ^ 2) * C₂⁻¹ :=
                mul_le_mul_of_nonneg_right hle (inv_nonneg.mpr (le_of_lt hC₂pos))
            _ = 16 * z ^ 2 / C₂ := by rw [div_eq_mul_inv]
      _ ≤ 16 * z ^ 2 := by
          rw [div_le_iff₀ hC₂pos]
          nlinarith [mul_nonneg (sq_nonneg z) (show (0 : ℝ) ≤ C₂ - 1 by linarith)]
  have hLnn : (0 : ℝ) ≤ (Real.log (4 * z)) ^ 2 / (2 * C₂) :=
    div_nonneg (sq_nonneg _) (by linarith)
  have herr_nn : (0 : ℝ) ≤ (z + 1) * ((Real.log (4 * z)) ^ 2 / (2 * C₂)) / (16 * z ^ 2) := by
    apply div_nonneg _ (by positivity)
    exact mul_nonneg (by linarith) hLnn
  have hle : (Real.log (4 * z)) ^ 2 / (2 * C₂) ≤
      (Real.log (4 * z)) ^ 2 / (2 * C₂) /
        (1 - (z + 1) * ((Real.log (4 * z)) ^ 2 / (2 * C₂)) / (16 * z ^ 2)) := by
    rw [le_div_iff₀ (by linarith :
      (0 : ℝ) < 1 - (z + 1) * ((Real.log (4 * z)) ^ 2 / (2 * C₂)) / (16 * z ^ 2))]
    nlinarith [mul_nonneg hLnn herr_nn]
  exact le_trans hle hthr

/-- M1: the dyadic twin-prime count bound, in exactly the form of the draft's
    `block_sum_le` hypothesis. The constant is 196 + 16·C₂/(log 2)². -/
theorem m1_count_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
      (((Finset.Ioc (2 ^ k) (2 ^ (k + 1))).filter
        (fun n => Nat.Prime n ∧ Nat.Prime (n + 2))).card : ℝ)
        ≤ C * (2 : ℝ) ^ k / ((k : ℝ) + 1) ^ 2 := by
  classical
  have hC₂lb : (131 / 100 : ℝ) ≤ TaoFivePrimes.twinPrimeConstant :=
    PrimePairSieve.twin_prime_constant_lower_131
  have hC₂pos : (0 : ℝ) < TaoFivePrimes.twinPrimeConstant := by linarith
  have hC₂ne : TaoFivePrimes.twinPrimeConstant ≠ 0 := ne_of_gt hC₂pos
  have hCnn : (0 : ℝ) ≤ 16 * TaoFivePrimes.twinPrimeConstant / (Real.log 2) ^ 2 :=
    div_nonneg (mul_nonneg (by norm_num) (le_of_lt hC₂pos)) (sq_nonneg _)
  have hC0 : (0 : ℝ) ≤ 196 + 16 * TaoFivePrimes.twinPrimeConstant / (Real.log 2) ^ 2 := by
    linarith
  refine ⟨196 + 16 * TaoFivePrimes.twinPrimeConstant / (Real.log 2) ^ 2, hC0, ?_⟩
  intro k
  by_cases hk : k < 14
  · -- Small k: trivial count bound, absorbed by the 196.
    have hcard : ((Finset.Ioc (2 ^ k) (2 ^ (k + 1))).filter
        (fun n => Nat.Prime n ∧ Nat.Prime (n + 2))).card ≤ 2 ^ k := by
      calc _ ≤ (Finset.Ioc (2 ^ k) (2 ^ (k + 1))).card :=
            Finset.card_le_card (Finset.filter_subset _ _)
        _ = 2 ^ (k + 1) - 2 ^ k := Nat.card_Ioc _ _
        _ = 2 ^ k := by rw [pow_succ]; omega
    have hcardR : (((Finset.Ioc (2 ^ k) (2 ^ (k + 1))).filter
        (fun n => Nat.Prime n ∧ Nat.Prime (n + 2))).card : ℝ) ≤ (2 : ℝ) ^ k := by
      have h : (((Finset.Ioc (2 ^ k) (2 ^ (k + 1))).filter
          (fun n => Nat.Prime n ∧ Nat.Prime (n + 2))).card : ℝ) ≤ (2 : ℝ) ^ k := by
        exact_mod_cast hcard
      exact h
    have hk14 : ((k : ℝ) + 1) ^ 2 ≤ 196 := by
      have hk13 : k ≤ (13 : ℕ) := by omega
      have hk' : (k : ℝ) ≤ 13 := by exact_mod_cast hk13
      have h1 : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
      calc ((k : ℝ) + 1) ^ 2 ≤ (14 : ℝ) ^ 2 := pow_le_pow_left₀ h1 (by linarith) 2
        _ = 196 := by norm_num
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < ((k : ℝ) + 1) ^ 2)]
    calc (((Finset.Ioc (2 ^ k) (2 ^ (k + 1))).filter
          (fun n => Nat.Prime n ∧ Nat.Prime (n + 2))).card : ℝ) * ((k : ℝ) + 1) ^ 2
        ≤ (2 : ℝ) ^ k * ((k : ℝ) + 1) ^ 2 :=
          mul_le_mul_of_nonneg_right hcardR (by positivity)
      _ ≤ (2 : ℝ) ^ k * 196 :=
          mul_le_mul_of_nonneg_left hk14 (by positivity)
      _ = 196 * (2 : ℝ) ^ k := by ring
      _ ≤ (196 + 16 * TaoFivePrimes.twinPrimeConstant / (Real.log 2) ^ 2) * (2 : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · -- Large k: the PrimePairSieve argument with x = 2^(k+1).
    push Not at hk
    set x : ℕ := 2 ^ (k + 1) with hx_def
    have hx16 : 16 ≤ x := by
      rw [hx_def]
      calc 16 ≤ 2 ^ 15 := by norm_num
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hx25600 : 25600 ≤ x := by
      rw [hx_def]
      calc 25600 ≤ 2 ^ 15 := by norm_num
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h160 : (160 : ℝ) ≤ Real.sqrt (x : ℝ) := by
      have h : Real.sqrt 25600 = 160 := by
        have h25600 : (25600 : ℝ) = 160 ^ 2 := by norm_num
        rw [h25600, Real.sqrt_sq (by norm_num)]
      rw [← h]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hx25600)
    have hz40 : 40 ≤ Real.sqrt (x : ℝ) / 4 := by linarith
    -- The pair-count bound at d = 2, with numerator product = 1.
    have hpc := PrimePairSieve_prime_pair_count_base_reciprocal_bound x 2 hx16
      (by norm_num) (by norm_num)
    have hnum : (∏ p ∈ (2 : ℕ).primeFactors,
        if 2 < p then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1) = 1 := by
      have h2 : (2 : ℕ).primeFactors = {2} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        constructor
        · exact Nat.mem_primeFactors.mpr ⟨Nat.prime_two, by norm_num, by norm_num⟩
        · intro p hp
          rw [Nat.mem_primeFactors] at hp
          obtain ⟨hpp, hpd, _⟩ := hp
          exact (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp hpd
      rw [h2, Finset.prod_singleton]
      simp
    rw [hnum, one_mul] at hpc
    -- The threshold lower bound for the same denominator sum.
    have hthr := PrimePairSieve.reciprocal_base_denominator_dominates_threshold
      (Real.sqrt (x : ℝ) / 4) hz40
    have hDgeL := denom_lower (Real.sqrt (x : ℝ) / 4)
      TaoFivePrimes.twinPrimeConstant _ hz40 hC₂lb hthr
    -- Positivity facts for the denominator manipulations.
    have h4z : 4 * (Real.sqrt (x : ℝ) / 4) = Real.sqrt (x : ℝ) := by
      rw [← mul_div_assoc, div_eq_iff (by norm_num : (4 : ℝ) ≠ 0)]
      ring
    have hlogx_pos : (0 : ℝ) < Real.log (x : ℝ) := by
      apply Real.log_pos
      exact_mod_cast (by omega : 1 < x)
    have hlogx_ne : Real.log (x : ℝ) ≠ 0 := ne_of_gt hlogx_pos
    have hlog4z : Real.log (4 * (Real.sqrt (x : ℝ) / 4)) = Real.log (x : ℝ) / 2 := by
      rw [h4z, Real.log_sqrt (Nat.cast_nonneg x)]
    have hlog4z_pos : (0 : ℝ) < Real.log (4 * (Real.sqrt (x : ℝ) / 4)) := by
      rw [hlog4z]; linarith
    have hLpos : (0 : ℝ) < (Real.log (4 * (Real.sqrt (x : ℝ) / 4))) ^ 2 /
        (2 * TaoFivePrimes.twinPrimeConstant) :=
      div_pos (pow_pos hlog4z_pos 2) (by linarith)
    have hDpos : (0 : ℝ) < ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt (x : ℝ) / 4⌋₊,
        (if Squarefree q then ∏ p ∈ q.primeFactors,
          if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2) else 0) /
          (1 + (q : ℝ) / (Real.sqrt (x : ℝ) / 4)) := by
      linarith
    have hxD : (x : ℝ) / (∑ q ∈ Finset.Icc 1 ⌊Real.sqrt (x : ℝ) / 4⌋₊,
        (if Squarefree q then ∏ p ∈ q.primeFactors,
          if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2) else 0) /
          (1 + (q : ℝ) / (Real.sqrt (x : ℝ) / 4)))
        ≤ (x : ℝ) / ((Real.log (4 * (Real.sqrt (x : ℝ) / 4))) ^ 2 /
          (2 * TaoFivePrimes.twinPrimeConstant)) := by
      rw [div_le_div_iff₀ hDpos hLpos]
      exact mul_le_mul_of_nonneg_left hDgeL (Nat.cast_nonneg x)
    have hxL : (x : ℝ) / ((Real.log (4 * (Real.sqrt (x : ℝ) / 4))) ^ 2 /
        (2 * TaoFivePrimes.twinPrimeConstant))
        = 8 * TaoFivePrimes.twinPrimeConstant * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 := by
      rw [hlog4z]
      field_simp
      ring
    have hlogx : Real.log (x : ℝ) = ((k : ℝ) + 1) * Real.log 2 := by
      rw [hx_def]
      simp [Real.log_pow]
    have hxR : (x : ℝ) = (2 : ℝ) ^ (k + 1) := by
      rw [hx_def]; simp
    have hmain : 8 * TaoFivePrimes.twinPrimeConstant * (x : ℝ) / (Real.log (x : ℝ)) ^ 2
        = (16 * TaoFivePrimes.twinPrimeConstant / (Real.log 2) ^ 2) * (2 : ℝ) ^ k /
          ((k : ℝ) + 1) ^ 2 := by
      rw [hlogx, hxR]
      have h2 : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by rw [pow_succ]; ring
      rw [h2, mul_pow]
      have hkp1 : ((k : ℝ) + 1) ≠ 0 := ne_of_gt (by positivity)
      have hlog2ne : Real.log 2 ≠ 0 :=
        ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
      field_simp
      ring
    -- The block is contained in the pair-count range, plus at most one
    -- boundary element (n = x - 1); n = x itself is even, hence not prime.
    have hsub : (Finset.Ioc (2 ^ k) x).filter
        (fun n => Nat.Prime n ∧ Nat.Prime (n + 2))
        ⊆ (Finset.range (x + 1)).filter
          (fun n => Nat.Prime n ∧ Nat.Prime (n + 2) ∧ n + 2 ≤ x) ∪ {x - 1} := by
      intro n hn
      rw [Finset.mem_filter] at hn
      obtain ⟨hnIoc, hnP1, hnP2⟩ := hn
      rw [Finset.mem_Ioc] at hnIoc
      rw [Finset.mem_union]
      by_cases hle : n + 2 ≤ x
      · left
        rw [Finset.mem_filter]
        refine ⟨?_, hnP1, hnP2, hle⟩
        rw [Finset.mem_range]
        omega
      · right
        rw [Finset.mem_singleton]
        have hnx : n ≠ x := by
          intro hnx
          have h2dvd : 2 ∣ n := by
            rw [hnx, hx_def]
            exact ⟨2 ^ k, by rw [pow_succ]; ring⟩
          have h2eq : 2 = n := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hnP1).mp h2dvd
          have h2k : 2 ^ 14 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
          have h214 : (2 : ℕ) ^ 14 = 16384 := by norm_num
          omega
        omega
    have hcard_le : ((Finset.Ioc (2 ^ k) x).filter
        (fun n => Nat.Prime n ∧ Nat.Prime (n + 2))).card
        ≤ ((Finset.range (x + 1)).filter
          (fun n => Nat.Prime n ∧ Nat.Prime (n + 2) ∧ n + 2 ≤ x)).card + 1 := by
      calc _ ≤ (((Finset.range (x + 1)).filter
            (fun n => Nat.Prime n ∧ Nat.Prime (n + 2) ∧ n + 2 ≤ x)) ∪ {x - 1}).card :=
            Finset.card_le_card hsub
        _ ≤ ((Finset.range (x + 1)).filter
            (fun n => Nat.Prime n ∧ Nat.Prime (n + 2) ∧ n + 2 ≤ x)).card +
            ({x - 1} : Finset ℕ).card :=
            Finset.card_union_le _ _
        _ = _ + 1 := by rw [Finset.card_singleton]
    have hsum_eq : (∑ n ∈ Finset.range (x + 1),
        (if Nat.Prime n ∧ Nat.Prime (n + 2) ∧ n + 2 ≤ x then (1 : ℝ) else 0))
        = (((Finset.range (x + 1)).filter
          (fun n => Nat.Prime n ∧ Nat.Prime (n + 2) ∧ n + 2 ≤ x)).card : ℝ) := by
      rw [← Finset.sum_filter]
      simp
    have hcardR : (((Finset.Ioc (2 ^ k) x).filter
        (fun n => Nat.Prime n ∧ Nat.Prime (n + 2))).card : ℝ)
        ≤ (∑ n ∈ Finset.range (x + 1),
          (if Nat.Prime n ∧ Nat.Prime (n + 2) ∧ n + 2 ≤ x then (1 : ℝ) else 0)) + 1 := by
      have h1 : (((Finset.Ioc (2 ^ k) x).filter
          (fun n => Nat.Prime n ∧ Nat.Prime (n + 2))).card : ℝ)
          ≤ (((Finset.range (x + 1)).filter
            (fun n => Nat.Prime n ∧ Nat.Prime (n + 2) ∧ n + 2 ≤ x)).card : ℝ) + 1 := by
        have h : (((Finset.Ioc (2 ^ k) x).filter
            (fun n => Nat.Prime n ∧ Nat.Prime (n + 2))).card : ℝ)
            ≤ (((Finset.range (x + 1)).filter
              (fun n => Nat.Prime n ∧ Nat.Prime (n + 2) ∧ n + 2 ≤ x)).card : ℝ) + 1 := by
          exact_mod_cast hcard_le
        exact h
      rw [← hsum_eq] at h1
      exact h1
    -- The additive error √x/4 + 2, absorbed by 196·2^k/(k+1)².
    have herr2 : Real.sqrt (x : ℝ) / 4 + 2 ≤ 196 * (2 : ℝ) ^ k / ((k : ℝ) + 1) ^ 2 := by
      obtain ⟨j, rfl⟩ : ∃ j, k = 14 + j := Nat.exists_eq_add_of_le hk
      have hbounds := aux_bounds j
      have hx15 : x = 2 ^ (15 + j) := by rw [hx_def]; congr 1; omega
      have hxR2 : (x : ℝ) = (2 : ℝ) ^ (15 + j) := by rw [hx15]; simp
      have hcast : (((14 + j : ℕ) : ℝ) + 1) = (15 : ℝ) + j := by push_cast; ring
      rw [hcast]
      set u : ℝ := (2 : ℝ) ^ (14 + j) / ((15 : ℝ) + j) ^ 2 with hu_def
      have h15pos : (0 : ℝ) < (15 : ℝ) + j := by positivity
      have hu21 : (2 / 21 : ℝ) ≤ u := by
        rw [hu_def, le_div_iff₀ (by positivity : (0 : ℝ) < ((15 : ℝ) + j) ^ 2)]
        calc (2 / 21) * ((15 : ℝ) + j) ^ 2
            ≤ (2 / 21) * ((21 / 2) * (2 : ℝ) ^ (14 + j)) :=
              mul_le_mul_of_nonneg_left hbounds.1 (by norm_num)
          _ = (2 : ℝ) ^ (14 + j) := by ring
      have hu_pos : (0 : ℝ) < u := by linarith
      have h1 : (700 * u) ^ 2 ≤ (784 * u - 8) ^ 2 := by
        apply pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 700 * u) _ 2
        linarith
      have h2 : (2 : ℝ) ^ (15 + j) ≤ (700 * u) ^ 2 := by
        have hu2 : u ^ 2 = (2 : ℝ) ^ (14 + j) * (2 : ℝ) ^ (14 + j) /
            (((15 : ℝ) + j) ^ 2 * ((15 : ℝ) + j) ^ 2) := by
          rw [hu_def, div_pow, pow_two, pow_two]
        have h700 : (700 * u) ^ 2 = 490000 * u ^ 2 := by ring
        rw [h700, hu2]
        have hnum2 : (2 : ℝ) ^ (15 + j) = (2 : ℝ) ^ (14 + j) * 2 := by
          rw [show 15 + j = (14 + j) + 1 by omega, pow_succ]
        rw [hnum2, ← mul_div_assoc, le_div_iff₀ (by positivity :
          (0 : ℝ) < ((15 : ℝ) + j) ^ 2 * ((15 : ℝ) + j) ^ 2)]
        have hB : ((15 : ℝ) + j) ^ 2 * ((15 : ℝ) + j) ^ 2 = ((15 : ℝ) + j) ^ 4 := by
          ring
        rw [hB]
        calc (2 : ℝ) ^ (14 + j) * 2 * ((15 : ℝ) + j) ^ 4
            ≤ (2 : ℝ) ^ (14 + j) * 2 * (245000 * (2 : ℝ) ^ (14 + j)) :=
              mul_le_mul_of_nonneg_left hbounds.2 (by positivity)
          _ = 490000 * ((2 : ℝ) ^ (14 + j) * (2 : ℝ) ^ (14 + j)) := by ring
      have h3 : (x : ℝ) ≤ (784 * u - 8) ^ 2 := by
        calc (x : ℝ) = (2 : ℝ) ^ (15 + j) := hxR2
          _ ≤ (700 * u) ^ 2 := h2
          _ ≤ (784 * u - 8) ^ 2 := h1
      have h784nn : (0 : ℝ) ≤ 784 * u - 8 := by linarith
      have hsqrt : Real.sqrt (x : ℝ) ≤ 784 * u - 8 := by
        have h1 := Real.sqrt_le_sqrt h3
        rw [Real.sqrt_sq h784nn] at h1
        exact h1
      have hfin : Real.sqrt (x : ℝ) / 4 + 2 ≤ 196 * u := by linarith
      rw [mul_div_assoc, ← hu_def]
      exact hfin
    -- Assemble.
    calc (((Finset.Ioc (2 ^ k) x).filter
          (fun n => Nat.Prime n ∧ Nat.Prime (n + 2))).card : ℝ)
        ≤ (∑ n ∈ Finset.range (x + 1),
            (if Nat.Prime n ∧ Nat.Prime (n + 2) ∧ n + 2 ≤ x then (1 : ℝ) else 0)) + 1 :=
          hcardR
      _ ≤ ((x : ℝ) / (∑ q ∈ Finset.Icc 1 ⌊Real.sqrt (x : ℝ) / 4⌋₊,
            (if Squarefree q then ∏ p ∈ q.primeFactors,
              if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2) else 0) /
              (1 + (q : ℝ) / (Real.sqrt (x : ℝ) / 4))) +
            Real.sqrt (x : ℝ) / 4 + 1) + 1 := by linarith [hpc]
      _ = (x : ℝ) / (∑ q ∈ Finset.Icc 1 ⌊Real.sqrt (x : ℝ) / 4⌋₊,
            (if Squarefree q then ∏ p ∈ q.primeFactors,
              if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2) else 0) /
              (1 + (q : ℝ) / (Real.sqrt (x : ℝ) / 4))) +
            (Real.sqrt (x : ℝ) / 4 + 2) := by ring
      _ ≤ (x : ℝ) / ((Real.log (4 * (Real.sqrt (x : ℝ) / 4))) ^ 2 /
            (2 * TaoFivePrimes.twinPrimeConstant)) +
            (Real.sqrt (x : ℝ) / 4 + 2) := by linarith [hxD]
      _ = (16 * TaoFivePrimes.twinPrimeConstant / (Real.log 2) ^ 2) * (2 : ℝ) ^ k /
            ((k : ℝ) + 1) ^ 2 + (Real.sqrt (x : ℝ) / 4 + 2) := by
          rw [hxL, hmain]
      _ ≤ (16 * TaoFivePrimes.twinPrimeConstant / (Real.log 2) ^ 2) * (2 : ℝ) ^ k /
            ((k : ℝ) + 1) ^ 2 + 196 * (2 : ℝ) ^ k / ((k : ℝ) + 1) ^ 2 := by
          linarith [herr2]
      _ = (196 + 16 * TaoFivePrimes.twinPrimeConstant / (Real.log 2) ^ 2) *
            (2 : ℝ) ^ k / ((k : ℝ) + 1) ^ 2 := by ring

#print axioms m1_count_bound

/-- Brun's theorem: the sum of reciprocals of twin primes converges. -/
theorem solution :
    Summable (fun p : {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2)} => (p : ℝ)⁻¹) := by
  obtain ⟨C, hC, hcount⟩ := m1_count_bound
  exact brun_theorem_of_count_bound C hC hcount
