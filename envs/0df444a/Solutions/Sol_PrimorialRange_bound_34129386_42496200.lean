-- Prove2me | solution 1 for PrimorialRange.bound_34129386_42496200
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T07:05:32.583274+00:00
-- url     : https://prove2.me/submissions/0d8306ed-67b6-4b43-a2b1-e57dde1901fd

import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Zify
import Definitions.Def_ThetaCertCore
import Theorems.Thm_TaoFivePrimes_axler_chain_c1
import Theorems.Thm_TaoFivePrimes_axler_chain_c2
import Theorems.Thm_TaoFivePrimes_axler_chain_c3
import Theorems.Thm_TaoFivePrimes_axler_chain_c4a

set_option Elab.async false
set_option autoImplicit false

open Finset Real

namespace PrimC6R1

open DusartCert ThetaSieve

/-! ## Part 1: Soundness of `DusartCert.log_bounds` -/

lemma hasSum_log_atanh {y : ℝ} (hy : 1 ≤ y) :
    HasSum (fun j : ℕ => 2 * (1 / (2 * (j : ℝ) + 1)) * ((y - 1) / (y + 1)) ^ (2 * j + 1)) (Real.log y) := by
  have hz0 : 0 ≤ (y - 1) / (y + 1) := div_nonneg (by linarith) (by linarith)
  have hz1 : (y - 1) / (y + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have h := Real.hasSum_log_sub_log_of_abs_lt_one (x := (y - 1) / (y + 1)) (by rw [abs_of_nonneg hz0]; exact hz1)
  convert h using 1
  rw [← Real.log_div (by positivity) (by linarith)]
  congr 1
  field_simp; ring

lemma atanh_lower {y : ℝ} (hy : 1 ≤ y) (K : ℕ) :
    ∑ j ∈ range K, 2 * (1 / (2 * (j : ℝ) + 1)) * ((y - 1) / (y + 1)) ^ (2 * j + 1) ≤ Real.log y := by
  have hz0 : 0 ≤ (y - 1) / (y + 1) := div_nonneg (by linarith) (by linarith)
  exact sum_le_hasSum _ (fun j _ => by positivity) (hasSum_log_atanh hy)

lemma atanh_upper {y : ℝ} (hy : 1 ≤ y) (K : ℕ) :
    Real.log y ≤ ∑ j ∈ range K, 2 * (1 / (2 * (j : ℝ) + 1)) * ((y - 1) / (y + 1)) ^ (2 * j + 1) +
      2 * ((y - 1) / (y + 1)) ^ (2 * K + 1) / ((2 * K + 1) * (1 - ((y - 1) / (y + 1)) ^ 2)) := by
  set z := (y - 1) / (y + 1) with hz
  have hz0 : 0 ≤ z := div_nonneg (by linarith) (by linarith)
  have hz1 : z < 1 := by rw [hz, div_lt_one (by linarith)]; linarith
  have hS := hasSum_log_atanh hy
  rw [← hz] at hS
  have hsplit := hS.summable.sum_add_tsum_nat_add K
  rw [hS.tsum_eq] at hsplit
  rw [← hsplit]
  gcongr
  have hz2 : z ^ 2 < 1 := by nlinarith
  have hgeo : Summable fun j : ℕ => 2 * z ^ (2 * K + 1) / (2 * K + 1) * (z ^ 2) ^ j :=
    (summable_geometric_of_lt_one (by positivity) hz2).mul_left _
  have hle : ∀ j : ℕ, 2 * (1 / (2 * ((j + K : ℕ) : ℝ) + 1)) * z ^ (2 * (j + K) + 1) ≤
      2 * z ^ (2 * K + 1) / (2 * K + 1) * (z ^ 2) ^ j := by
    intro j
    rw [← pow_mul, show 2 * (j + K) + 1 = (2 * K + 1) + 2 * j by ring, pow_add]
    have h1 : 1 / (2 * ((j + K : ℕ) : ℝ) + 1) ≤ 1 / (2 * (K : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity); push_cast; linarith [show (0 : ℝ) ≤ j from Nat.cast_nonneg j]
    have h2 : 0 ≤ z ^ (2 * K + 1) * z ^ (2 * j) := by positivity
    calc 2 * (1 / (2 * ((j + K : ℕ) : ℝ) + 1)) * (z ^ (2 * K + 1) * z ^ (2 * j))
        ≤ 2 * (1 / (2 * (K : ℝ) + 1)) * (z ^ (2 * K + 1) * z ^ (2 * j)) := by gcongr
      _ = 2 * z ^ (2 * K + 1) / (2 * K + 1) * z ^ (2 * j) := by ring
  calc ∑' j : ℕ, 2 * (1 / (2 * ((j + K : ℕ) : ℝ) + 1)) * z ^ (2 * (j + K) + 1)
      ≤ ∑' j : ℕ, 2 * z ^ (2 * K + 1) / (2 * K + 1) * (z ^ 2) ^ j :=
        Summable.tsum_le_tsum hle (hgeo.of_nonneg_of_le (fun j => by positivity) hle) hgeo
    _ = 2 * z ^ (2 * K + 1) / ((2 * K + 1) * (1 - z ^ 2)) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hz2]
        have : (1 - z ^ 2) ≠ 0 := by linarith
        field_simp

lemma floor_div_le (N D : ℕ) (hD : 0 < D) : ((N / D : ℕ) : ℝ) ≤ (N : ℝ) / D := by
  rw [le_div_iff₀ (by exact_mod_cast hD)]; exact_mod_cast Nat.div_mul_le_self N D

lemma le_cdiv (N D : ℕ) (hD : 0 < D) : (N : ℝ) / D ≤ (cdiv N D : ℝ) := by
  rw [div_le_iff₀ (by exact_mod_cast hD)]
  have h2 := Nat.div_add_mod (N + D - 1) D
  have h3 := Nat.mod_lt (N + D - 1) hD
  have : N ≤ cdiv N D * D := by
    unfold cdiv; rw [Nat.mul_comm] at h2
    generalize (N + D - 1) / D * D = X at *; omega
  exact_mod_cast this

lemma lterm_real (Q a b j : ℕ) (hb : 0 < b) :
    (Q : ℝ) * (2 * (1 / (2 * (j : ℝ) + 1)) * ((a : ℝ) / b) ^ (2 * j + 1)) =
      ((2 * Q * a ^ (2 * j + 1) : ℕ) : ℝ) / (((2 * j + 1) * b ^ (2 * j + 1) : ℕ) : ℝ) := by
  have : (b : ℝ) ≠ 0 := by positivity
  push_cast; rw [div_pow]; field_simp

lemma lsumLo_le (Q a b : ℕ) (hb : 0 < b) : ∀ K, (lsumLo Q a b K : ℝ) ≤
    (Q : ℝ) * ∑ j ∈ range K, 2 * (1 / (2 * (j : ℝ) + 1)) * ((a : ℝ) / b) ^ (2 * j + 1) := by
  intro K; induction K with
  | zero => simp [lsumLo]
  | succ K ih =>
    rw [lsumLo, Nat.cast_add, sum_range_succ, mul_add, lterm_real Q a b K hb]
    have := floor_div_le (2 * Q * a ^ (2 * K + 1)) ((2 * K + 1) * b ^ (2 * K + 1)) (by positivity)
    unfold ltermLo; linarith

lemma lsumHi_ge (Q a b : ℕ) (hb : 0 < b) : ∀ K,
    (Q : ℝ) * ∑ j ∈ range K, 2 * (1 / (2 * (j : ℝ) + 1)) * ((a : ℝ) / b) ^ (2 * j + 1) ≤ (lsumHi Q a b K : ℝ) := by
  intro K; induction K with
  | zero => simp [lsumHi]
  | succ K ih =>
    rw [lsumHi, Nat.cast_add, sum_range_succ, mul_add, lterm_real Q a b K hb]
    have := le_cdiv (2 * Q * a ^ (2 * K + 1)) ((2 * K + 1) * b ^ (2 * K + 1)) (by positivity)
    unfold ltermHi; linarith

theorem logRed_bounds (Q num den : ℕ) (hd : 0 < den) (hle : den ≤ num) :
    (logRedLo Q num den : ℝ) ≤ Q * Real.log ((num : ℝ) / den) ∧
      Q * Real.log ((num : ℝ) / den) ≤ (logRedHi Q num den : ℝ) := by
  have hden : (0 : ℝ) < den := by exact_mod_cast hd
  have hy : (1 : ℝ) ≤ (num : ℝ) / den := by rw [le_div_iff₀ hden]; simp; exact_mod_cast hle
  have hb : 0 < num + den := by omega
  have hz : ((num : ℝ) / den - 1) / ((num : ℝ) / den + 1) = (((num - den : ℕ) : ℝ)) / ((num + den : ℕ) : ℝ) := by
    rw [Nat.cast_sub hle]; push_cast; field_simp
  have hQ : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
  constructor
  · have := atanh_lower hy nterms
    rw [hz] at this
    exact (lsumLo_le Q (num - den) (num + den) hb nterms).trans (mul_le_mul_of_nonneg_left this hQ)
  · have hu := atanh_upper hy nterms
    rw [hz] at hu
    have h1 := lsumHi_ge Q (num - den) (num + den) hb nterms
    set a := num - den; set b := num + den
    have hab : a < b := by omega
    have hb2 : 0 < b ^ 2 - a ^ 2 := by
      have : a ^ 2 < b ^ 2 := Nat.pow_lt_pow_left hab (by norm_num)
      omega
    have hrem := le_cdiv (2 * Q * a ^ (2 * nterms + 1) * b ^ 2) ((2 * nterms + 1) * b ^ (2 * nterms + 1) * (b ^ 2 - a ^ 2))
      (by positivity)
    have hremeq : (Q : ℝ) * (2 * ((a : ℝ) / b) ^ (2 * nterms + 1) / ((2 * nterms + 1) * (1 - ((a : ℝ) / b) ^ 2))) =
        ((2 * Q * a ^ (2 * nterms + 1) * b ^ 2 : ℕ) : ℝ) /
          (((2 * nterms + 1) * b ^ (2 * nterms + 1) * (b ^ 2 - a ^ 2) : ℕ) : ℝ) := by
      have hb0 : (b : ℝ) ≠ 0 := by positivity
      have hsub : ((b ^ 2 - a ^ 2 : ℕ) : ℝ) = (b : ℝ) ^ 2 - (a : ℝ) ^ 2 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      have hne : (b : ℝ) ^ 2 - (a : ℝ) ^ 2 ≠ 0 := by
        rw [← hsub]; exact_mod_cast hb2.ne'
      push_cast [hsub]
      simp only [div_pow]
      field_simp
    unfold logRedHi lrem
    rw [Nat.cast_add]
    calc (Q : ℝ) * Real.log ((num : ℝ) / den) ≤ (Q : ℝ) * (∑ j ∈ range nterms,
          2 * (1 / (2 * (j : ℝ) + 1)) * ((a : ℝ) / b) ^ (2 * j + 1) +
          2 * ((a : ℝ) / b) ^ (2 * nterms + 1) / ((2 * nterms + 1) * (1 - ((a : ℝ) / b) ^ 2))) :=
          mul_le_mul_of_nonneg_left hu hQ
      _ ≤ _ := by rw [mul_add, hremeq]; linarith

theorem log_bounds (Q num den k : ℕ) (h : redOK num den k = true) :
    (logLo Q num den k : ℝ) ≤ Q * Real.log ((num : ℝ) / den) ∧
      Q * Real.log ((num : ℝ) / den) ≤ (logHi Q num den k : ℝ) := by
  simp only [redOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, _⟩, hd⟩ := h
  have h2 := logRed_bounds Q 2 1 one_pos (by norm_num)
  have hk := logRed_bounds Q num (den * 2 ^ k) (by positivity) h1
  have hden : (0 : ℝ) < den := by exact_mod_cast hd
  have hsplit : Real.log ((num : ℝ) / den) = k * Real.log 2 + Real.log ((num : ℝ) / ((den * 2 ^ k : ℕ) : ℝ)) := by
    have hnum : (0 : ℝ) < num := by
      have : 0 < den * 2 ^ k := by positivity
      exact_mod_cast lt_of_lt_of_le this h1
    push_cast
    rw [Real.log_div hnum.ne' hden.ne', Real.log_div hnum.ne' (by positivity : (den : ℝ) * 2 ^ k ≠ 0),
      Real.log_mul hden.ne' (by positivity), Real.log_pow]; ring
  have hl2 : Real.log ((2 : ℕ) / ((1 : ℕ) : ℝ)) = Real.log 2 := by norm_num
  rw [hl2] at h2
  unfold logLo logHi
  push_cast
  rw [hsplit]
  constructor
  · nlinarith [h2.1, hk.1, show (0 : ℝ) ≤ k from Nat.cast_nonneg k]
  · nlinarith [h2.2, hk.2, show (0 : ℝ) ≤ k from Nat.cast_nonneg k]

/-! ## Part 2: Soundness of SWAR popcount, pmask, and segmented sieve -/

def encF (f : ℕ) : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, c => c 0 + 2 ^ f * encF f n (fun j => c (j + 1))

lemma encF_testBit {f : ℕ} (hf : 0 < f) : ∀ (n : ℕ) (c : ℕ → ℕ), (∀ j, c j < 2 ^ f) → ∀ i,
    (encF f n c).testBit i = (decide (i / f < n) && (c (i / f)).testBit (i % f)) := by
  intro n; induction n with
  | zero => intro c _ i; simp [encF]
  | succ n ih =>
    intro c hc i
    rw [encF, Nat.add_comm, Nat.testBit_two_pow_mul_add _ (hc 0)]
    split_ifs with h
    · have h1 : i / f = 0 := Nat.div_eq_of_lt h
      have h2 : i % f = i := Nat.mod_eq_of_lt h
      simp [h1, h2]
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 h)
      rw [ih _ (fun j => hc (j + 1)), Nat.add_sub_cancel_left, Nat.add_div_left _ hf, Nat.add_mod_left]
      simp

lemma encF_zero_fun (f : ℕ) : ∀ (n : ℕ) (c : ℕ → ℕ), (∀ j, c j = 0) → encF f n c = 0 := by
  intro n; induction n with
  | zero => intro c _; rfl
  | succ n ih => intro c hc; rw [encF, hc 0, ih _ (fun j => hc (j + 1))]; simp

lemma encF_pad (f : ℕ) : ∀ (n k : ℕ) (c : ℕ → ℕ), (∀ j, n ≤ j → c j = 0) → encF f (n + k) c = encF f n c := by
  intro n; induction n with
  | zero => intro k c hc; simp only [Nat.zero_add]; rw [encF_zero_fun f k c (fun j => hc j (Nat.zero_le _))]; rfl
  | succ n ih =>
    intro k c hc
    rw [show n + 1 + k = (n + k) + 1 by ring, encF, encF, ih k _ (fun j hj => hc (j + 1) (by omega))]

lemma encF_pad_eq {g W : ℕ} {c : ℕ → ℕ} (hc : ∀ j, W ≤ j * g → c j = 0) {n m : ℕ} (hn : W ≤ n * g) (hm : W ≤ m * g) :
    encF g n c = encF g m c := by
  have hn0 : W ≤ min n m * g := by
    rcases le_total n m with h | h
    · rw [min_eq_left h]; exact hn
    · rw [min_eq_right h]; exact hm
  have hz : ∀ j, min n m ≤ j → c j = 0 := fun j hj => hc j (le_trans hn0 (Nat.mul_le_mul_right g hj))
  calc encF g n c = encF g (min n m + (n - min n m)) c := by congr 1; omega
    _ = encF g (min n m) c := encF_pad g _ _ c hz
    _ = encF g (min n m + (m - min n m)) c := (encF_pad g _ _ c hz).symm
    _ = encF g m c := by congr 1; omega

lemma encF_add (f : ℕ) : ∀ (n : ℕ) (a b : ℕ → ℕ), encF f n a + encF f n b = encF f n (fun j => a j + b j) := by
  intro n; induction n with
  | zero => intro a b; rfl
  | succ n ih => intro a b; simp only [encF]; rw [← ih]; ring

lemma encF_mul (f : ℕ) : ∀ (n : ℕ) (a : ℕ → ℕ) (d : ℕ), encF f n a * d = encF f n (fun j => a j * d) := by
  intro n; induction n with
  | zero => intro a d; simp [encF]
  | succ n ih => intro a d; simp only [encF]; rw [← ih]; ring

lemma encF_regroup (f : ℕ) : ∀ (n : ℕ) (c : ℕ → ℕ),
    encF f (2 * n) c = encF (2 * f) n (fun j => c (2 * j) + 2 ^ f * c (2 * j + 1)) := by
  intro n; induction n with
  | zero => intro c; rfl
  | succ n ih =>
    intro c
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by ring, encF, encF, ih, encF]
    have e : (fun j => c (j + 1 + 1)) = (fun j => c (j + 2)) := rfl
    have e2 : (fun j => c (2 * j + 2) + 2 ^ f * c (2 * j + 1 + 2)) =
        (fun j => c (2 * (j + 1)) + 2 ^ f * c (2 * (j + 1) + 1)) := by
      funext j; rw [show 2 * j + 2 = 2 * (j + 1) by ring, show 2 * j + 1 + 2 = 2 * (j + 1) + 1 by ring]
    simp only [e, e2, Nat.mul_zero, Nat.zero_add, Nat.mul_one]
    rw [two_mul f, pow_add]; ring

lemma encF_and {f : ℕ} (hf : 0 < f) (n : ℕ) (a b : ℕ → ℕ) (ha : ∀ j, a j < 2 ^ f) (hb : ∀ j, b j < 2 ^ f) :
    encF f n a &&& encF f n b = encF f n (fun j => a j &&& b j) := by
  have hab : ∀ j, (a j &&& b j) < 2 ^ f := fun j => lt_of_le_of_lt Nat.and_le_left (ha j)
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, encF_testBit hf n a ha, encF_testBit hf n b hb, encF_testBit hf n _ hab, Nat.testBit_and]
  cases decide (i / f < n) <;> simp

lemma encF_shift (f : ℕ) (n : ℕ) (c : ℕ → ℕ) (h0 : c 0 < 2 ^ f) :
    encF f (n + 1) c >>> f = encF f n (fun j => c (j + 1)) := by
  rw [Nat.shiftRight_eq_div_pow, encF, Nat.add_mul_div_left _ _ (Nat.two_pow_pos f), Nat.div_eq_of_lt h0, Nat.zero_add]

lemma geom_eq_encF {p : ℕ} (hp : 1 ≤ p) (n : ℕ) : geom p n = encF p n (fun _ => 1) := by
  have key : ∀ n, encF p n (fun _ => 1) * (2 ^ p - 1) + 1 = 2 ^ (p * n) := by
    intro n; induction n with
    | zero => simp [encF]
    | succ n ih =>
      have h1 : 1 ≤ 2 ^ p := Nat.one_le_two_pow
      simp only [encF] at ih ⊢
      rw [Nat.mul_succ, pow_add]
      zify [h1] at ih ⊢
      push_cast at ih ⊢
      nlinarith [ih]
  have h2 : 0 < 2 ^ p - 1 := by
    have : 2 ≤ 2 ^ p := by calc 2 = 2 ^ 1 := by norm_num
                             _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp
    omega
  unfold geom
  rw [← key n, Nat.add_sub_cancel, Nat.mul_div_cancel _ h2]

def cnt (x W f j : ℕ) : ℕ := ((Finset.Ico (j * f) ((j + 1) * f)).filter (fun i => i < W ∧ x.testBit i = true)).card

lemma cnt_le (x W f j : ℕ) : cnt x W f j ≤ f := by
  unfold cnt
  refine (Finset.card_filter_le _ _).trans ?_
  simp [Nat.card_Ico]; ring_nf; omega

lemma cnt_lt {x W f j : ℕ} (hf : 0 < f) : cnt x W f j < 2 ^ f := lt_of_le_of_lt (cnt_le x W f j) (Nat.lt_two_pow_self)

lemma cnt_zero_of {x W f j : ℕ} (h : W ≤ j * f) : cnt x W f j = 0 := by
  unfold cnt
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i hi; simp only [Finset.mem_Ico] at hi; omega

lemma cnt_split (x W f j : ℕ) : cnt x W (2 * f) j = cnt x W f (2 * j) + cnt x W f (2 * j + 1) := by
  unfold cnt
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    rw [← Finset.filter_union, Finset.Ico_union_Ico_eq_Ico (by nlinarith) (by nlinarith)]
    congr 1; ring_nf
  · rw [Finset.disjoint_left]; intro i h1 h2
    simp only [Finset.mem_filter, Finset.mem_Ico] at h1 h2; nlinarith [h1.1.2, h2.1.1]

lemma round_eq {x W k : ℕ} :
    (encF (2 ^ k) (2 * (W / (2 * 2 ^ k) + 1)) (cnt x W (2 ^ k)) &&& swarMask W k) +
      ((encF (2 ^ k) (2 * (W / (2 * 2 ^ k) + 1)) (cnt x W (2 ^ k)) >>> 2 ^ k) &&& swarMask W k) =
      encF (2 * 2 ^ k) (W / (2 * 2 ^ k) + 1) (cnt x W (2 * 2 ^ k)) := by
  unfold swarMask
  have hf : 0 < 2 ^ k := Nat.two_pow_pos k
  generalize 2 ^ k = f at hf ⊢
  have hW : W < (W / (2 * f) + 1) * (2 * f) := by
    rw [Nat.add_mul, Nat.one_mul]; exact Nat.lt_div_mul_add (by omega)
  generalize W / (2 * f) + 1 = N at hW ⊢
  set alt : ℕ → ℕ := fun j => if j % 2 = 0 then 2 ^ f - 1 else 0 with halt_def
  have halt : ∀ j, alt j < 2 ^ f := fun j => by
    simp only [alt]; have := Nat.two_pow_pos f; split_ifs <;> omega
  have hM : geom (2 * f) N * (2 ^ f - 1) = encF f (2 * N) alt := by
    rw [encF_regroup, geom_eq_encF (by omega), encF_mul]
    congr 1; funext j
    simp only [alt, Nat.mul_mod_right, if_true, show (2 * j + 1) % 2 = 1 by omega, one_ne_zero, if_false,
      mul_zero, add_zero, one_mul]
  have hc : ∀ j, cnt x W f j < 2 ^ f := fun j => cnt_lt hf
  have hE : encF f (2 * N) (cnt x W f) &&& encF f (2 * N) alt = encF (2 * f) N (fun j => cnt x W f (2 * j)) := by
    rw [encF_and hf _ _ _ hc halt, encF_regroup]
    congr 1; funext j
    simp only [alt, Nat.mul_mod_right, if_true, show (2 * j + 1) % 2 = 1 by omega, one_ne_zero, if_false,
      Nat.and_zero, mul_zero, add_zero, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (hc _)]
  have hsh : encF f (2 * N) (cnt x W f) >>> f = encF f (2 * N) (fun j => cnt x W f (j + 1)) := by
    have h2N : 2 * N = (2 * N - 1) + 1 := by
      rcases Nat.eq_zero_or_pos N with rfl | h
      · simp at hW
      · omega
    rw [h2N, encF_shift _ _ _ (hc 0)]
    refine (encF_pad f _ 1 _ (fun j hj => cnt_zero_of ?_)).symm
    have h1 : 2 * N * f ≤ (j + 1) * f := Nat.mul_le_mul_right f (by omega)
    have h2 : N * (2 * f) = 2 * N * f := by ring
    omega
  have hO : encF f (2 * N) (fun j => cnt x W f (j + 1)) &&& encF f (2 * N) alt =
      encF (2 * f) N (fun j => cnt x W f (2 * j + 1)) := by
    rw [encF_and hf _ _ _ (fun j => hc _) halt, encF_regroup]
    congr 1; funext j
    simp only [alt, Nat.mul_mod_right, if_true, show (2 * j + 1) % 2 = 1 by omega, one_ne_zero, if_false,
      Nat.and_zero, mul_zero, add_zero, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (hc _)]
  rw [hM, hE, hsh, hO, encF_add]
  congr 1; funext j; rw [cnt_split]

lemma pcAux_eq {x W : ℕ} : ∀ (fuel k : ℕ),
    pcAux W fuel k (encF (2 ^ k) (2 * (W / (2 * 2 ^ k) + 1)) (cnt x W (2 ^ k))) =
      encF (2 ^ (k + fuel)) (2 * (W / (2 * 2 ^ (k + fuel)) + 1)) (cnt x W (2 ^ (k + fuel))) := by
  intro fuel; induction fuel with
  | zero => intro k; rfl
  | succ fuel ih =>
    intro k
    rw [pcAux, round_eq, show k + (fuel + 1) = (k + 1) + fuel by ring, ← ih (k + 1)]
    congr 1
    rw [pow_succ, mul_comm (2 ^ k) 2]
    have hf : 0 < 2 * 2 ^ k := by positivity
    apply encF_pad_eq (g := 2 * 2 ^ k) (W := W) (fun j hj => cnt_zero_of hj)
    · have := Nat.lt_div_mul_add (a := W) (b := 2 * 2 ^ k) hf; nlinarith
    · have := Nat.lt_div_mul_add (a := W) (b := 2 * (2 * 2 ^ k)) (by positivity); nlinarith

theorem popcountW_eq {W x : ℕ} (hx : x < 2 ^ W) :
    popcountW W x = ((Finset.range W).filter (fun i => x.testBit i = true)).card := by
  have hbase : x = encF (2 ^ 0) (2 * (W / (2 * 2 ^ 0) + 1)) (cnt x W (2 ^ 0)) := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [encF_testBit (by norm_num) _ _ (fun j => cnt_lt (by norm_num))]
    simp only [pow_zero, Nat.div_one, Nat.mod_one]
    by_cases hi : i < W
    · have hcnt : cnt x W 1 i = if x.testBit i = true then 1 else 0 := by
        unfold cnt
        rw [show Finset.Ico (i * 1) ((i + 1) * 1) = {i} by ext; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega,
          Finset.filter_singleton]
        by_cases hb : x.testBit i = true <;> simp [hb, hi]
      rw [hcnt]
      have : i < 2 * (W / 2 + 1) := by omega
      by_cases hb : x.testBit i = true <;> simp [hb, this]
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (not_lt.1 hi))),
        cnt_zero_of (by simpa using not_lt.1 hi)]
      simp
  unfold popcountW
  nth_rewrite 1 [hbase]
  rw [pcAux_eq, Nat.zero_add]
  set K := Nat.log2 W + 1
  have hK : W < 2 ^ K := Nat.lt_log2_self
  rw [encF_pad_eq (g := 2 ^ K) (W := W) (fun j hj => cnt_zero_of hj) (m := 1)
    (by have := Nat.lt_div_mul_add (a := W) (b := 2 * 2 ^ K) (by positivity); nlinarith) (by simpa using hK.le)]
  simp only [encF, mul_zero, add_zero]
  unfold cnt
  congr 1
  ext i; simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_range, Nat.zero_mul, Nat.zero_add, Nat.one_mul]
  constructor
  · rintro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨Nat.zero_le _, by omega⟩, h1, h2⟩

def fm (L p : ℕ) : ℕ :=
  let m0 := max (p * p) (((L + p - 1) / p) * p)
  if m0 % 2 == 0 then m0 + p else m0

lemma pmask_eq (L W p : ℕ) : pmask L W p =
    if L + 2 * W ≤ fm L p then 0 else geom p ((W - 1 - (fm L p - L) / 2) / p + 1) <<< ((fm L p - L) / 2) := rfl

lemma fm_spec {L p : ℕ} (hL : L % 2 = 1) (hp : p % 2 = 1) :
    fm L p % 2 = 1 ∧ p ∣ fm L p ∧ L ≤ fm L p ∧ p * p ≤ fm L p ∧
      ∀ n, n % 2 = 1 → p ∣ n → L ≤ n → p * p ≤ n → fm L p ≤ n := by
  have hp0 : 0 < p := by omega
  set c := (L + p - 1) / p with hc
  have hcL : L ≤ c * p := by
    have := Nat.lt_div_mul_add (a := L + p - 1) hp0; rw [← hc] at this; omega
  have hcmin : ∀ q, L ≤ q * p → c ≤ q := by
    intro q hq
    have : c < q + 1 := (Nat.div_lt_iff_lt_mul hp0).2 (by rw [Nat.add_mul, Nat.one_mul]; omega)
    omega
  have hm0d : p ∣ max (p * p) (c * p) := by
    rcases le_total (p * p) (c * p) with h | h
    · rw [max_eq_right h]; exact Dvd.intro_left c rfl
    · rw [max_eq_left h]; exact Dvd.intro p rfl
  have hm0min : ∀ n, p ∣ n → L ≤ n → p * p ≤ n → max (p * p) (c * p) ≤ n := by
    rintro n ⟨q, rfl⟩ h1 h2
    exact max_le h2 (by rw [mul_comm p q]; exact Nat.mul_le_mul_right p (hcmin q (by rw [mul_comm]; exact h1)))
  unfold fm
  simp only [← hc]
  generalize hm0 : max (p * p) (c * p) = m0 at hm0d hm0min
  have hm0p : p * p ≤ m0 := hm0 ▸ le_max_left _ _
  have hm0L : L ≤ m0 := hm0 ▸ le_trans hcL (le_max_right _ _)
  by_cases he : m0 % 2 = 0
  · have hb : (m0 % 2 == 0) = true := by simp [he]
    rw [if_pos hb]
    refine ⟨by omega, Nat.dvd_add hm0d (dvd_refl p), by omega, by omega, ?_⟩
    intro n hn hpn hLn hpp
    have h1 := hm0min n hpn hLn hpp
    have h2 : m0 ≠ n := by omega
    obtain ⟨a, rfl⟩ := hm0d; obtain ⟨b, rfl⟩ := hpn
    have : a < b := by
      by_contra hab; rw [not_lt] at hab
      have := Nat.mul_le_mul_left p hab; omega
    have := Nat.mul_le_mul_left p (show a + 1 ≤ b by omega); rw [Nat.mul_add, Nat.mul_one] at this; exact this
  · have hb : (m0 % 2 == 0) = false := by simp [he]
    rw [if_neg (by simp [hb])]
    exact ⟨by omega, hm0d, hm0L, hm0p, fun n _ h1 h2 h3 => hm0min n h1 h2 h3⟩

theorem pmask_testBit {L W p : ℕ} (hL : L % 2 = 1) (hp : p % 2 = 1) (i : ℕ) :
    (pmask L W p).testBit i = decide (i < W ∧ p ∣ L + 2 * i ∧ p * p ≤ L + 2 * i) := by
  obtain ⟨hmo, hmd, hmL, hmp, hmin⟩ := fm_spec hL hp
  have hp0 : 0 < p := by omega
  rw [pmask_eq]
  generalize fm L p = m at hmo hmd hmL hmp hmin
  split_ifs with hz
  · rw [Nat.zero_testBit]; symm; rw [decide_eq_false_iff_not]
    rintro ⟨hi, hd, hpp⟩
    have := hmin _ (by omega) hd (by omega) hpp; omega
  · generalize hi0 : (m - L) / 2 = i0
    have hm : m = L + 2 * i0 := by omega
    have hi0W : i0 < W := by omega
    rw [Nat.testBit_shiftLeft, geom_eq_encF (by omega),
      encF_testBit hp0 _ _ (fun _ => Nat.one_lt_two_pow (by omega))]
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.testBit_one_eq_true_iff_self_eq_zero]
    have hcop : Nat.Coprime p 2 := Nat.coprime_two_right.2 (Nat.odd_iff.2 hp)
    constructor
    · rintro ⟨hge, hq, hr⟩
      obtain ⟨q, hq'⟩ : p ∣ i - i0 := Nat.dvd_of_mod_eq_zero hr
      have hiq : i = i0 + p * q := by omega
      have hqle : q ≤ (W - 1 - i0) / p := by
        have : (i - i0) / p = q := by rw [hq']; exact Nat.mul_div_cancel_left q hp0
        omega
      have hpq : p * q ≤ W - 1 - i0 := by
        have := Nat.div_mul_le_self (W - 1 - i0) p
        have := Nat.mul_le_mul_left p hqle; rw [mul_comm p ((W - 1 - i0) / p)] at this; omega
      refine ⟨by omega, ?_, by omega⟩
      rw [show L + 2 * i = m + p * (2 * q) by rw [hm, hiq]; ring]
      exact Nat.dvd_add hmd (Dvd.intro _ rfl)
    · rintro ⟨hiW, hd, hpp⟩
      have hle := hmin _ (by omega) hd (by omega) hpp
      have hge : i0 ≤ i := by omega
      have h2 : p ∣ (i - i0) * 2 := by
        have : (L + 2 * i) - m = (i - i0) * 2 := by omega
        rw [← this]; exact Nat.dvd_sub hd hmd
      have h3 : p ∣ i - i0 := hcop.dvd_of_dvd_mul_right h2
      refine ⟨hge, ?_, Nat.mod_eq_zero_of_dvd h3⟩
      have := Nat.div_le_div_right (c := p) (show i - i0 ≤ W - 1 - i0 by omega)
      omega

def sortedB : List ℕ → Bool
  | p :: q :: r => decide (p < q) && sortedB (q :: r)
  | _ => true

lemma sortedB_tail {p : ℕ} {ps : List ℕ} (h : sortedB (p :: ps) = true) : sortedB ps = true := by
  match ps, h with
  | [], _ => rfl
  | q :: r, h => simp only [sortedB, Bool.and_eq_true] at h; exact h.2

lemma sortedB_head : ∀ {p : ℕ} {ps : List ℕ}, sortedB (p :: ps) = true → ∀ q ∈ ps, p < q
  | _, [], _, q, hq => by simp at hq
  | p, r :: rs, h, q, hq => by
    simp only [sortedB, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.1 hq with rfl | hq
    · exact h.1
    · exact lt_trans h.1 (sortedB_head h.2 q hq)

def oddB (ps : List ℕ) : Bool := ps.all (fun p => p % 2 == 1 && decide (3 ≤ p))

lemma oddB_mem {ps : List ℕ} (h : oddB ps = true) {p : ℕ} (hp : p ∈ ps) : p % 2 = 1 ∧ 3 ≤ p := by
  have := List.all_eq_true.1 h p hp
  simpa [Bool.and_eq_true] using this

theorem compMask_testBit {L W : ℕ} (hL : L % 2 = 1) (i : ℕ) : ∀ (ps : List ℕ), sortedB ps = true → oddB ps = true →
    (compMask L W ps).testBit i = decide (i < W ∧ ∃ p ∈ ps, p ∣ L + 2 * i ∧ p * p ≤ L + 2 * i)
  | [], _, _ => by simp [compMask]
  | p :: ps, hs, ho => by
    have hpo := oddB_mem ho List.mem_cons_self
    have ho' : oddB ps = true := by
      unfold oddB at ho ⊢; rw [List.all_cons, Bool.and_eq_true] at ho; exact ho.2
    unfold compMask
    split_ifs with hz
    · rw [Nat.zero_testBit]; symm; rw [decide_eq_false_iff_not]
      rintro ⟨hi, q, hq, _, hqq⟩
      have hpq : p ≤ q := by
        rcases List.mem_cons.1 hq with rfl | hq
        · exact le_refl _
        · exact (sortedB_head hs q hq).le
      have := Nat.mul_le_mul hpq hpq; omega
    · rw [Nat.testBit_or, pmask_testBit hL hpo.1, compMask_testBit hL i ps (sortedB_tail hs) ho']
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_cons]
      constructor
      · rintro (⟨h1, h2, h3⟩ | ⟨h1, q, hq, h2, h3⟩)
        · exact ⟨h1, p, Or.inl rfl, h2, h3⟩
        · exact ⟨h1, q, Or.inr hq, h2, h3⟩
      · rintro ⟨h1, q, rfl | hq, h2, h3⟩
        · exact Or.inl ⟨h1, h2, h3⟩
        · exact Or.inr ⟨h1, q, hq, h2, h3⟩

lemma smallPrimes_sorted : sortedB smallPrimes = true := by decide +kernel
lemma smallPrimes_odd : oddB smallPrimes = true := by decide +kernel

theorem survivors_testBit {L W : ℕ} (hL : L % 2 = 1) (i : ℕ) :
    (survivors L W).testBit i =
      decide (i < W ∧ ¬ ∃ p ∈ smallPrimes, p ∣ L + 2 * i ∧ p * p ≤ L + 2 * i) := by
  unfold survivors
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, compMask_testBit hL i _ smallPrimes_sorted smallPrimes_odd]
  by_cases hi : i < W <;> by_cases hx : ∃ p ∈ smallPrimes, p ∣ L + 2 * i ∧ p * p ≤ L + 2 * i <;> simp [hi, hx]

def bitmap : List ℕ → ℕ
  | [] => 0
  | q :: qs => (1 <<< ((q - 3) / 2)) ||| bitmap qs

lemma bitmap_mem : ∀ (qs : List ℕ), oddB qs = true → ∀ i, (bitmap qs).testBit i = true → 3 + 2 * i ∈ qs
  | [], _, i, h => by simp [bitmap] at h
  | q :: qs, ho, i, h => by
    have hq := oddB_mem ho List.mem_cons_self
    have ho' : oddB qs = true := by
      unfold oddB at ho ⊢; rw [List.all_cons, Bool.and_eq_true] at ho; exact ho.2
    rw [bitmap, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · rw [Nat.testBit_shiftLeft, Bool.and_eq_true, Nat.testBit_one_eq_true_iff_self_eq_zero] at h
      have : i = (q - 3) / 2 := by simp at h; omega
      rw [List.mem_cons]; left; omega
    · exact List.mem_cons_of_mem _ (bitmap_mem qs ho' i h)

lemma smallPrimes_bitmap : survivors 3 29999 = bitmap smallPrimes := by decide +kernel

theorem smallPrimes_complete {q : ℕ} (hq : q.Prime) (h3 : 3 ≤ q) (h6 : q < 60001) : q ∈ smallPrimes := by
  have hodd : q % 2 = 1 := by
    by_contra h
    have := hq.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero (by omega)); omega
  have hq' : 3 + 2 * ((q - 3) / 2) = q := by omega
  have hi : (survivors 3 29999).testBit ((q - 3) / 2) = true := by
    rw [survivors_testBit (by norm_num), decide_eq_true_eq, hq']
    refine ⟨by omega, ?_⟩
    rintro ⟨p, hp, hd, hpp⟩
    have hp3 := (oddB_mem smallPrimes_odd hp).2
    rcases hq.eq_one_or_self_of_dvd p hd with h | h
    · omega
    · subst h; nlinarith
  rw [smallPrimes_bitmap] at hi
  have := bitmap_mem _ smallPrimes_odd _ hi
  rwa [hq'] at this

theorem survivors_prime {L W : ℕ} (hL : L % 2 = 1) (h3 : 3 ≤ L) (hB : L + 2 * W ≤ 60001 * 60001) {i : ℕ}
    (hi : i < W) : (survivors L W).testBit i = true ↔ (L + 2 * i).Prime := by
  rw [survivors_testBit hL, decide_eq_true_eq]
  constructor
  · rintro ⟨_, hno⟩
    by_contra hnp
    set n := L + 2 * i with hn
    have hn1 : n ≠ 1 := by omega
    have hq := Nat.minFac_prime hn1
    have hsq : n.minFac ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnp
    have hq2 : n.minFac ≠ 2 := by
      intro h2; have := Nat.minFac_dvd n; rw [h2] at this; omega
    have hq3 : 3 ≤ n.minFac := by have := hq.two_le; omega
    have hq6 : n.minFac < 60001 := by
      by_contra h; rw [not_lt] at h
      have := Nat.mul_le_mul h h; rw [sq] at hsq; omega
    exact hno ⟨_, smallPrimes_complete hq hq3 hq6, Nat.minFac_dvd n, by rw [← sq]; exact hsq⟩
  · intro hp
    refine ⟨hi, ?_⟩
    rintro ⟨p, hmem, hd, hpp⟩
    have hp3 := (oddB_mem smallPrimes_odd hmem).2
    rcases hp.eq_one_or_self_of_dvd p hd with h | h
    · omega
    · rw [h] at hpp; nlinarith [hp.two_le]

/-! ## Part 3: Theta upper-bound propagation and base chain soundness -/

noncomputable def th (n : ℕ) : ℝ := Chebyshev.theta n

lemma th_succ (n : ℕ) : th (n + 1) = th n + if (n + 1).Prime then Real.log (n + 1) else 0 := by
  unfold th Chebyshev.theta
  rw [Nat.floor_natCast, Nat.floor_natCast, Finset.sum_filter, Finset.sum_filter,
    Finset.sum_Ioc_succ_top (Nat.zero_le n)]
  push_cast; rfl

noncomputable def oblock (a w : ℕ) : ℝ := ∑ i ∈ range w, if (a + 2 * i).Prime then Real.log (a + 2 * i : ℕ) else 0

lemma th_block {a : ℕ} (ha : 3 ≤ a) (hodd : a % 2 = 1) : ∀ w, th (a + 2 * w - 1) = th (a - 1) + oblock a w := by
  intro w; induction w with
  | zero => simp [oblock]
  | succ w ih =>
    have e1 : a + 2 * (w + 1) - 1 = (a + 2 * w - 1 + 1) + 1 := by omega
    have e2 : a + 2 * w - 1 + 1 = a + 2 * w := by omega
    have hs : oblock a (w + 1) = oblock a w + (if (a + 2 * w).Prime then Real.log (a + 2 * w : ℕ) else 0) :=
      Finset.sum_range_succ _ _
    have hne : ¬ (a + 2 * w + 1).Prime := by
      intro hp
      have := hp.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero (by omega)); omega
    rw [e1, th_succ, th_succ, ih, hs, e2, if_neg hne,
      show ((a + 2 * w - 1 : ℕ) : ℝ) + 1 = ((a + 2 * w : ℕ) : ℝ) by rw [← Nat.cast_add_one, e2]]
    ring

def ocount (a w : ℕ) : ℕ := ((range w).filter (fun i => (a + 2 * i).Prime)).card

lemma oblock_le {a w : ℕ} (ha : 1 ≤ a) :
    oblock a w ≤ (ocount a w : ℝ) * Real.log (a + 2 * w : ℕ) := by
  unfold oblock ocount
  rw [← Finset.sum_filter]
  have hc : ∀ i ∈ (range w).filter (fun i => (a + 2 * i).Prime),
      Real.log (a + 2 * i : ℕ) ≤ Real.log (a + 2 * w : ℕ) := by
    intro i hi
    rw [Finset.mem_filter, Finset.mem_range] at hi
    have h0 : (0 : ℝ) < a := by exact_mod_cast ha
    have hiw : (i : ℝ) ≤ w := by exact_mod_cast hi.1.le
    exact Real.log_le_log (by push_cast; positivity) (by push_cast; linarith)
  have := Finset.sum_le_card_nsmul _ _ _ hc
  simpa [nsmul_eq_mul] using this

lemma Q_pos : (0 : ℝ) < Q := by unfold Q; positivity

lemma LLo_le {n : ℕ} (hn : 1 ≤ n) : (LLo n : ℝ) ≤ Q * Real.log n := by
  have h := log_bounds Q n 1 (Nat.log2 n) (by
    simp only [redOK, Bool.and_eq_true, decide_eq_true_eq, one_mul]
    exact ⟨⟨Nat.log2_self_le (by omega), by have := @Nat.lt_log2_self n; rw [pow_succ] at this; omega⟩, one_pos⟩)
  simpa [LLo] using h.1

lemma le_LHi {n : ℕ} (hn : 1 ≤ n) : Q * Real.log n ≤ (LHi n : ℝ) := by
  have h := log_bounds Q n 1 (Nat.log2 n) (by
    simp only [redOK, Bool.and_eq_true, decide_eq_true_eq, one_mul]
    exact ⟨⟨Nat.log2_self_le (by omega), by have := @Nat.lt_log2_self n; rw [pow_succ] at this; omega⟩, one_pos⟩)
  simpa [LHi] using h.2

lemma le_logLinHi {L b logL : ℕ} (hL : 1 ≤ L) (hLb : L ≤ b)
    (hlogL : (Q : ℝ) * Real.log L ≤ logL) :
    (Q : ℝ) * Real.log b ≤ ((logL + cdiv (Q * (b - L)) L : ℕ) : ℝ) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (lt_of_lt_of_le hL hLb)
  have h1 : Real.log ((b : ℝ) / L) ≤ (b : ℝ) / L - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hb0 hL0)
  have h2 : Real.log (b : ℝ) = Real.log L + Real.log ((b : ℝ) / L) := by
    rw [Real.log_div hb0.ne' hL0.ne']; ring
  have h3 : (b : ℝ) / L - 1 = ((b - L : ℕ) : ℝ) / L := by
    rw [Nat.cast_sub hLb]; field_simp
  have h4 : (Q : ℝ) * (((b - L : ℕ) : ℝ) / L) = ((Q * (b - L) : ℕ) : ℝ) / L := by
    push_cast; ring
  have h5 := le_cdiv (Q * (b - L)) L (by omega)
  have hQ0 : (0 : ℝ) ≤ Q := le_of_lt Q_pos
  have hmul : (Q : ℝ) * Real.log ((b : ℝ) / L) ≤ (Q : ℝ) * (((b - L : ℕ) : ℝ) / L) := by
    rw [← h3]; exact mul_le_mul_of_nonneg_left h1 hQ0
  have h2Q : (Q : ℝ) * Real.log (b : ℝ) = (Q : ℝ) * Real.log L + (Q : ℝ) * Real.log ((b : ℝ) / L) := by
    rw [h2]; ring
  push_cast
  linarith

lemma prodSmall_eq : ∀ (k L x : ℕ), prodSmall k L x = ∏ i ∈ range k, if x.testBit i then L + 2 * i else 1 := by
  intro k; induction k with
  | zero => intro L x; rfl
  | succ k ih =>
    intro L x
    rw [prodSmall, ih, Finset.prod_range_succ']
    rw [mul_comm]
    congr 1
    · apply Finset.prod_congr rfl; intro i _
      rw [Nat.testBit_div_two]; congr 1; ring
    · by_cases h : x % 2 = 1
      · have : x.testBit 0 = true := by rw [Nat.testBit_zero]; simp [h]
        simp [h, this]
      · have : x.testBit 0 = false := by rw [Nat.testBit_zero]; simp [h]
        simp [h, this]

lemma chunk_prod {L W off w : ℕ} (hL : L % 2 = 1) (h3 : 3 ≤ L) (hB : L + 2 * W ≤ 60001 * 60001)
    (hw : off + w ≤ W) : prodSmall w (L + 2 * off) ((survivors L W >>> off) % 2 ^ w) =
      ∏ i ∈ range w, if (L + 2 * off + 2 * i).Prime then L + 2 * off + 2 * i else 1 := by
  rw [prodSmall_eq]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  simp only [hi, decide_true, Bool.true_and]
  have := survivors_prime hL h3 hB (show off + i < W by omega)
  rw [show L + 2 * (off + i) = L + 2 * off + 2 * i by ring] at this
  by_cases hp : (L + 2 * off + 2 * i).Prime
  · rw [if_pos (this.2 hp), if_pos hp]
  · have : ¬ (survivors L W).testBit (off + i) = true := fun h => hp (this.1 h)
    rw [if_neg this, if_neg hp]

lemma log_chunk (a w : ℕ) (ha : 1 ≤ a) :
    Real.log ((∏ i ∈ range w, if (a + 2 * i).Prime then a + 2 * i else 1 : ℕ) : ℝ) = oblock a w := by
  rw [Nat.cast_prod, Real.log_prod]
  · unfold oblock; apply Finset.sum_congr rfl; intro i _; split_ifs <;> simp
  · intro i _; exact Nat.cast_ne_zero.2 (by split_ifs <;> omega)

def HiInv (hi a : ℕ) : Prop := (Q : ℝ) * th (a - 1) ≤ hi

theorem accSeg_hi_sound {L W : ℕ} (hL : L % 2 = 1) (h3 : 3 ≤ L) (hB : L + 2 * W ≤ 60001 * 60001) :
    ∀ (n lo hi off rem lo' hi' : ℕ), off + rem = W → rem ≤ 64 * n →
      accSeg lo hi (L + 2 * off) (survivors L W >>> off) rem n = (lo', hi') → HiInv hi (L + 2 * off) →
      HiInv hi' (L + 2 * W) := by
  intro n; induction n with
  | zero =>
    intro lo hi off rem lo' hi' hsum hrem h hI
    simp only [accSeg, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [show W = off by omega]; exact hI
  | succ n ih =>
    intro lo hi off rem lo' hi' hsum hrem h hI
    rw [accSeg] at h
    split_ifs at h with h0
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [show W = off by omega]; exact hI
    · dsimp only at h
      set w := min 64 rem with hw
      set a := L + 2 * off with ha_def
      have hw1 : off + w ≤ W := by omega
      rw [chunk_prod hL h3 hB hw1] at h
      have hP := log_chunk a w (by omega)
      have hPpos : 1 ≤ (∏ i ∈ range w, if (a + 2 * i).Prime then a + 2 * i else 1) := by
        apply Finset.one_le_prod''; intro i; split_ifs <;> omega
      have hhi := le_LHi hPpos
      rw [hP] at hhi
      have hblk := th_block (a := a) (by omega) (by omega) w
      have hInv : HiInv (hi + LHi (∏ i ∈ range w, if (a + 2 * i).Prime then a + 2 * i else 1))
          (L + 2 * (off + w)) := by
        unfold HiInv at hI ⊢
        rw [show L + 2 * (off + w) - 1 = a + 2 * w - 1 by omega, hblk]
        push_cast; nlinarith [hI]
      exact ih _ _ (off + w) (rem - w) lo' hi' (by omega) (by omega)
        (by rw [show L + 2 * (off + w) = a + 2 * w by omega, Nat.shiftRight_add]; exact h) hInv

theorem bseg_hi_sound (s : Seg) (h : s.bok = true) (hI : HiInv s.hi s.L) : HiInv s.hi' (s.L + 2 * s.W) := by
  unfold Seg.bok baseSeg at h
  split_ifs at h with hr
  · simp only [segRange, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hr
    obtain ⟨⟨hL, h3⟩, hB⟩ := hr
    have h' : accSeg s.lo s.hi s.L (survivors s.L s.W) s.W (s.W / 64 + 1) = (s.lo', s.hi') := by simpa using h
    exact accSeg_hi_sound hL h3 hB (s.W / 64 + 1) s.lo s.hi 0 s.W s.lo' s.hi' (by omega) (by omega)
      (by simpa using h') (by simpa using hI)
  · simp at h

def chainEnd : Seg → List Seg → Seg
  | s, [] => s
  | _, t :: r => chainEnd t r

theorem bchain_hi_sound : ∀ (l : List Seg) (s : Seg), chainOK (s :: l) = true → (∀ x ∈ s :: l, x.bok = true) →
    HiInv s.hi s.L → HiInv (chainEnd s l).hi' ((chainEnd s l).L + 2 * (chainEnd s l).W) := by
  intro l; induction l with
  | nil => intro s _ hok hI; exact bseg_hi_sound s (hok s List.mem_cons_self) hI
  | cons t r ih =>
    intro s hc hok hI
    simp only [chainOK, Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨⟨h1, _⟩, h3⟩, hc⟩ := hc
    have hs := bseg_hi_sound s (hok s List.mem_cons_self) hI
    have hIt : HiInv t.hi t.L := by rw [← h1, ← h3]; exact hs
    exact ih t hc (fun x hx => hok x (List.mem_cons_of_mem _ hx)) hIt

lemma HiInv_three : HiInv (LHi 2) 3 := by
  have h2 : th 2 = Real.log 2 := by
    have e1 := th_succ 1; have e0 := th_succ 0
    have hz : th 0 = 0 := by unfold th; simp
    rw [e0, hz] at e1; rw [show (2 : ℕ) = 1 + 1 from rfl, e1]
    simp [Nat.prime_two]; norm_num
  unfold HiInv; rw [show 3 - 1 = 2 from rfl, h2]
  simpa using le_LHi (n := 2) (by norm_num)

/-! ## Part 4: Fast linear-log window checker and soundness -/

lemma window_count {L W off w : ℕ} (hL : L % 2 = 1) (h3 : 3 ≤ L) (hB : L + 2 * W ≤ 60001 * 60001)
    (hw : off + w ≤ W) : popcountW w ((survivors L W >>> off) % 2 ^ w) = ocount (L + 2 * off) w := by
  rw [popcountW_eq (Nat.mod_lt _ (Nat.two_pow_pos w))]
  unfold ocount; congr 1
  apply Finset.filter_congr; intro i hi
  rw [Finset.mem_range] at hi
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  simp only [hi, decide_true, Bool.true_and]
  rw [survivors_prime hL h3 hB (by omega : off + i < W), show L + 2 * (off + i) = L + 2 * off + 2 * i by ring]

/-- Windowed linear-log primorial checker over `k` windows of width `w`. -/
def primWin (c A L logL w : Nat) : Nat → Nat → Nat → Nat → Option Nat
  | 0, _, hi, _ => some hi
  | k + 1, a, hi, x =>
    let b := a + 2 * w
    let cnt := popcountW w (x % 2 ^ w)
    let logb := logL + cdiv (Q * (b - L)) L
    let hi' := hi + cnt * logb
    if decide (A + 1 < b) && !decide (hi' < (a - 1) * c) then none
    else primWin c A L logL w k b hi' (x >>> w)

def primSeg (c A L k w hi : Nat) : Option Nat :=
  let W := k * w
  if segRange 3 L W then
    primWin c A L (LHi L) w k L hi (survivors L W)
  else none

def primChain (c A k w : Nat) : Nat → Nat → Nat → Bool
  | 0, _, _ => true
  | n + 1, L, hi =>
    match primSeg c A L k w hi with
    | none => false
    | some hi' => primChain c A k w n (L + 2 * (k * w)) hi'

theorem primWin_sound {c A L W logL w : ℕ} (hL : L % 2 = 1) (h3 : 3 ≤ L) (hB : L + 2 * W ≤ 60001 * 60001)
    (hlogL : (Q : ℝ) * Real.log L ≤ logL) :
    ∀ (k off hi hi_end : ℕ), off + k * w ≤ W →
      primWin c A L logL w k (L + 2 * off) hi (survivors L W >>> off) = some hi_end →
      HiInv hi (L + 2 * off) →
      HiInv hi_end (L + 2 * (off + k * w)) ∧
        ∀ n : ℕ, A < n → L + 2 * off ≤ n → n < L + 2 * (off + k * w) → (Q : ℝ) * th n < n * c := by
  intro k; induction k with
  | zero =>
    intro off hi hi_end _ h hI
    simp only [primWin, Option.some.injEq] at h
    subst h
    refine ⟨by simpa using hI, fun n _ hlo hhi => by omega⟩
  | succ k ih =>
    intro off hi hi_end hsum h hI
    rw [primWin] at h
    set a := L + 2 * off with ha_def
    set b := a + 2 * w with hb_def
    have hcnt := window_count hL h3 hB (show off + w ≤ W by nlinarith)
    rw [← ha_def] at hcnt
    rw [hcnt] at h
    set logb := logL + cdiv (Q * (b - L)) L with hlogb_def
    set hi' := hi + ocount a w * logb with hhi'_def
    split_ifs at h with hfail
    have hok : A + 1 < b → hi' < (a - 1) * c := by
      intro hAb
      by_contra hnot
      have : (decide (A + 1 < b) && !decide (hi' < (a - 1) * c)) = true := by
        simp [hAb, hnot]
      exact hfail this
    have hInv' : HiInv hi' b := by
      unfold HiInv at hI ⊢
      have hblk := th_block (a := a) (by omega) (by omega) w
      have hob := oblock_le (a := a) (w := w) (by omega)
      have hLb : (Q : ℝ) * Real.log (b : ℕ) ≤ (logb : ℝ) := le_logLinHi (by omega) (by omega) hlogL
      have hc0 : (0 : ℝ) ≤ ocount a w := Nat.cast_nonneg _
      have hQ0 : (0 : ℝ) ≤ Q := le_of_lt Q_pos
      rw [show b - 1 = a + 2 * w - 1 by omega, hblk, mul_add]
      have hstep : (Q : ℝ) * oblock a w ≤ (ocount a w : ℝ) * (logb : ℝ) := by
        calc (Q : ℝ) * oblock a w ≤ Q * ((ocount a w : ℝ) * Real.log (a + 2 * w : ℕ)) :=
              mul_le_mul_of_nonneg_left hob hQ0
          _ = (ocount a w : ℝ) * (Q * Real.log (b : ℕ)) := by rw [hb_def]; ring
          _ ≤ (ocount a w : ℝ) * (logb : ℝ) := mul_le_mul_of_nonneg_left hLb hc0
      rw [hhi'_def]; push_cast; linarith
    have hrec := ih (off + w) hi' hi_end (by nlinarith)
      (by rw [show L + 2 * (off + w) = b by omega, Nat.shiftRight_add]; exact h)
      (by rw [show L + 2 * (off + w) = b by omega]; exact hInv')
    have heq_end : off + (k + 1) * w = off + w + k * w := by ring
    rw [heq_end]
    refine ⟨hrec.1, fun n hAn hlo hhi => ?_⟩
    by_cases hin : n < b
    · have hchk : hi' < (a - 1) * c := hok (by omega)
      have hmono : th n ≤ th (b - 1) := by
        unfold th; exact Chebyshev.theta_mono (by exact_mod_cast (by omega : n ≤ b - 1))
      have hp' : (hi' : ℝ) < ((a - 1 : ℕ) : ℝ) * c := by exact_mod_cast hchk
      have hLle : ((a - 1 : ℕ) : ℝ) * c ≤ (n : ℝ) * c :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : a - 1 ≤ n)) (Nat.cast_nonneg c)
      calc (Q : ℝ) * th n ≤ Q * th (b - 1) := mul_le_mul_of_nonneg_left hmono (le_of_lt Q_pos)
        _ ≤ hi' := hInv'
        _ < ((a - 1 : ℕ) : ℝ) * c := hp'
        _ ≤ n * c := hLle
    · exact hrec.2 n hAn (by omega) hhi

theorem primSeg_sound {c A L k w hi hi' : ℕ} (h : primSeg c A L k w hi = some hi') (hI : HiInv hi L) :
    HiInv hi' (L + 2 * (k * w)) ∧
      ∀ n : ℕ, A < n → L ≤ n → n < L + 2 * (k * w) → (Q : ℝ) * th n < n * c := by
  unfold primSeg at h
  dsimp only at h
  split_ifs at h with hr
  · simp only [segRange, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hr
    obtain ⟨⟨hL, h3⟩, hB⟩ := hr
    have hlogL := le_LHi (n := L) (by omega)
    have hres := primWin_sound (w := w) hL h3 hB hlogL k 0 hi hi' (by omega) (by simpa using h) (by simpa using hI)
    simpa using hres

theorem primChain_sound {c A k w : ℕ} : ∀ (nsegs L hi : ℕ),
    primChain c A k w nsegs L hi = true → HiInv hi L →
    ∀ n : ℕ, A < n → L ≤ n → n < L + nsegs * (2 * (k * w)) → (Q : ℝ) * th n < n * c := by
  intro nsegs; induction nsegs with
  | zero => intro L hi _ _ n _ hlo hhi; omega
  | succ m ih =>
    intro L hi h hI n hAn hlo hhi
    rw [primChain] at h
    cases hs : primSeg c A L k w hi with
    | none => rw [hs] at h; simp at h
    | some hi' =>
      rw [hs] at h
      have h1 := primSeg_sound hs hI
      by_cases hin : n < L + 2 * (k * w)
      · exact h1.2 n hAn hlo hin
      · exact ih (L + 2 * (k * w)) hi' h h1.1 n hAn (by omega) (by nlinarith)

lemma c_le (h : LHi 25 ≤ LLo 68) : ((LLo 68 - LHi 25 : ℕ) : ℝ) ≤ Q * Real.log (68 / 25) := by
  have h68 := LLo_le (n := 68) (by norm_num)
  have h25 := le_LHi (n := 25) (by norm_num)
  rw [Nat.cast_sub h, Real.log_div (by norm_num) (by norm_num), mul_sub]
  push_cast at h68 h25 ⊢; linarith

lemma primorial_of_theta (n : ℕ) (hn : 0 < n) (h : th n < n * Real.log (68 / 25)) :
    primorial n * 25 ^ n < 68 ^ n := by
  have hth : th n = Real.log (primorial n) := by
    unfold th; rw [Chebyshev.theta_eq_log_primorial]; simp
  rw [hth] at h
  have hP : (0 : ℝ) < primorial n := by exact_mod_cast primorial_pos n
  have key : Real.log ((primorial n : ℝ) * 25 ^ n) < Real.log ((68 : ℝ) ^ n) := by
    rw [Real.log_mul hP.ne' (by positivity), Real.log_pow, Real.log_pow,
      Real.log_div (by norm_num) (by norm_num)] at *
    nlinarith
  have := (Real.log_lt_log_iff (by positivity) (by positivity)).1 key
  exact_mod_cast this

/-! ## Part 5: Axler checkpoint + kernel cert for `(34129386, 42496200]` -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

lemma HiInv_of_axler {x0 U0 L0 : ℕ} (hL0 : L0 - 1 ≤ x0)
    (h : (1000000 : ℝ) * Chebyshev.theta (x0 : ℝ) ≤ (U0 : ℝ)) :
    HiInv (cdiv (Q * U0) 1000000) L0 := by
  unfold HiInv th
  have hmono : Chebyshev.theta ((L0 - 1 : ℕ) : ℝ) ≤ Chebyshev.theta (x0 : ℝ) :=
    Chebyshev.theta_mono (by exact_mod_cast hL0)
  have h1 : (Q : ℝ) * Chebyshev.theta ((L0 - 1 : ℕ) : ℝ) ≤ (Q : ℝ) * ((U0 : ℝ) / 1000000) := by
    have : Chebyshev.theta (x0 : ℝ) ≤ (U0 : ℝ) / 1000000 := by linarith
    exact mul_le_mul_of_nonneg_left (hmono.trans this) (le_of_lt Q_pos)
  have h2 : (Q : ℝ) * ((U0 : ℝ) / 1000000) = ((Q * U0 : ℕ) : ℝ) / ((1000000 : ℕ) : ℝ) := by
    push_cast; ring
  have h3 := le_cdiv (Q * U0) 1000000 (by norm_num)
  linarith

private theorem ax_c1 : (154635160747 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (154970 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (154970 : ℝ) ≤ (154642599361 : ℝ) := TaoFivePrimes.axler_chain_c1.1
private theorem ax_c2 : (1697867131810 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (1699362 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (1699362 : ℝ) ≤ (1697951293771 : ℝ) := (TaoFivePrimes.axler_chain_c2 ax_c1).1
private theorem ax_c3 : (17382708166135 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (17387265 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (17387265 : ℝ) ≤ (17383459384328 : ℝ) := (TaoFivePrimes.axler_chain_c3 ax_c2).1
private theorem ax_top : (34123262759331 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (34129386 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (34129386 : ℝ) ≤ (34124678342292 : ℝ) := (TaoFivePrimes.axler_chain_c4a ax_c3).1

lemma hi_eq : cdiv (Q * 34124678342292) 1000000 = 629489207977919636898569490 := by decide

lemma hiInv_start : HiInv 629489207977919636898569490 34129387 := by
  rw [← hi_eq]; exact HiInv_of_axler (x0 := 34129386) (by omega) (by exact_mod_cast ax_top.2)

lemma cval : LLo 68 - LHi 25 = 18458400208034708012 := by decide +kernel
lemma cpos : LHi 25 ≤ LLo 68 := by decide +kernel

theorem cert_range :
    primChain 18458400208034708012 34129386 16 8192 32 34129387 629489207977919636898569490 = true := by decide +kernel

end PrimC6R1

theorem solution (n : ℕ) (hn : 34129386 < n) (hn' : n ≤ 42496200) :
    primorial n * 25 ^ n < 68 ^ n := by
  have hQ := PrimC6R1.primChain_sound 32 34129387 629489207977919636898569490
    PrimC6R1.cert_range PrimC6R1.hiInv_start n hn (by omega) (by omega)
  have hcq := PrimC6R1.c_le PrimC6R1.cpos
  rw [PrimC6R1.cval] at hcq
  have h2 : (ThetaSieve.Q : ℝ) * PrimC6R1.th n < ThetaSieve.Q * (n * Real.log (68 / 25)) := by
    calc (ThetaSieve.Q : ℝ) * PrimC6R1.th n < (n : ℝ) * (18458400208034708012 : ℕ) := hQ
      _ ≤ (n : ℝ) * (ThetaSieve.Q * Real.log (68 / 25)) := mul_le_mul_of_nonneg_left hcq (Nat.cast_nonneg n)
      _ = ThetaSieve.Q * (n * Real.log (68 / 25)) := by ring
  exact PrimC6R1.primorial_of_theta n (by omega) (lt_of_mul_lt_mul_left h2 (le_of_lt PrimC6R1.Q_pos))
