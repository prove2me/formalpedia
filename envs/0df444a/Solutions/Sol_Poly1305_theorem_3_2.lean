-- Prove2me | solution 1 for Poly1305.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-24T08:03:36.824999+00:00
-- url     : https://prove2.me/submissions/b37e6391-9371-4e19-a98b-dfb64e6d8a1c

import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_Poly1305Bernstein
import Theorems.Thm_Poly1305_chunk_mem_Icc

section
section
namespace Poly1305.HashThm32

open Polynomial

/-- Base-256 digits with a trailing leading term `256^n * c`. -/
theorem digit_aux (n : ℕ) : ∀ (f : ℕ → ℕ) (c s : ℕ), (∀ t, f t < 256) → s < n →
    ((∑ t ∈ Finset.range n, 256 ^ t * f t) + 256 ^ n * c) / 256 ^ s % 256 = f s := by
  induction n with
  | zero => intro f c s _ hs; omega
  | succ n ih =>
    intro f c s hf hs
    have hrec : (∑ t ∈ Finset.range (n + 1), 256 ^ t * f t) + 256 ^ (n + 1) * c =
        f 0 + 256 * ((∑ t ∈ Finset.range n, 256 ^ t * f (t + 1)) + 256 ^ n * c) := by
      rw [Finset.sum_range_succ', mul_add, Finset.mul_sum]
      have : ∀ t ∈ Finset.range n, 256 ^ (t + 1) * f (t + 1) = 256 * (256 ^ t * f (t + 1)) :=
        fun t _ => by ring
      rw [Finset.sum_congr rfl this]
      ring
    rw [hrec]
    rcases s with _ | s
    · simp only [pow_zero, Nat.div_one]
      have := hf 0
      omega
    · rw [pow_succ', ← Nat.div_div_eq_div_mul]
      have h0 := hf 0
      rw [show (f 0 + 256 * ((∑ t ∈ Finset.range n, 256 ^ t * f (t + 1)) + 256 ^ n * c)) / 256 =
          (∑ t ∈ Finset.range n, 256 ^ t * f (t + 1)) + 256 ^ n * c by omega]
      exact ih (fun t => f (t + 1)) c s (fun t => hf _) (by omega)

theorem sum_lt (f : ℕ → ℕ) (hf : ∀ t, f t < 256) (n : ℕ) :
    ∑ t ∈ Finset.range n, 256 ^ t * f t < 256 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have h1 : 256 ^ n * f n ≤ 256 ^ n * 255 := Nat.mul_le_mul_left _ (by have := hf n; omega)
    nlinarith

theorem byteAt_lt (m : Message) (k : ℕ) : byteAt m k < 256 := (m.getD k 0).isLt

/-- The number of bytes in chunk `i`. -/
def width (m : Message) (i : ℕ) : ℕ := if i ≤ m.length / 16 then 16 else m.length % 16

theorem chunk_eq (m : Message) (i : ℕ) :
    chunk m i = (∑ t ∈ Finset.range (width m i), 256 ^ t * byteAt m (16 * i - 16 + t)) +
      256 ^ (width m i) * 1 := by
  have h : ∀ t, (2 : ℕ) ^ (8 * t) = 256 ^ t := fun t => by rw [pow_mul]; norm_num
  unfold chunk width
  split_ifs <;> simp only [h, mul_one] <;> norm_num

theorem chunk_digit (m : Message) (j : ℕ) (hj : j < m.length) :
    chunk m (j / 16 + 1) / 256 ^ (j % 16) % 256 = byteAt m j := by
  rw [chunk_eq]
  have hw : j % 16 < width m (j / 16 + 1) := by
    unfold width; split_ifs <;> omega
  rw [digit_aux _ _ 1 _ (fun t => byteAt_lt _ _) hw]
  congr 1; omega

theorem chunk_bounds (m : Message) (i : ℕ) :
    256 ^ width m i ≤ chunk m i ∧ chunk m i < 2 * 256 ^ width m i := by
  rw [chunk_eq]
  have := sum_lt (fun t => byteAt m (16 * i - 16 + t)) (fun t => byteAt_lt _ _) (width m i)
  constructor <;> omega

theorem length_eq (m : Message) (hq : 1 ≤ numChunks m) :
    m.length = 16 * (numChunks m - 1) + width m (numChunks m) := by
  unfold numChunks width at *
  split_ifs <;> omega

theorem width_inj {a b x y : ℕ} (hx : 256 ^ a ≤ x ∧ x < 2 * 256 ^ a)
    (hy : 256 ^ b ≤ y ∧ y < 2 * 256 ^ b) (h : x = y) : a = b := by
  subst h
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hab | hab
  · have : 256 ^ (a + 1) ≤ 256 ^ b := Nat.pow_le_pow_right (by norm_num) hab
    rw [pow_succ] at this; omega
  · have : 256 ^ (b + 1) ≤ 256 ^ a := Nat.pow_le_pow_right (by norm_num) hab
    rw [pow_succ] at this; omega

/-- A message is determined by its number of chunks and its chunks. -/
theorem eq_of_chunks (m m' : Message) (hq : numChunks m = numChunks m')
    (hc : ∀ i, 1 ≤ i → i ≤ numChunks m → chunk m i = chunk m' i) : m = m' := by
  have hlen : m.length = m'.length := by
    by_cases h0 : numChunks m = 0
    · unfold numChunks at h0 hq; omega
    · have h1 : 1 ≤ numChunks m := Nat.one_le_iff_ne_zero.mpr h0
      have hw := width_inj (chunk_bounds m (numChunks m)) (chunk_bounds m' (numChunks m))
        (hc _ h1 le_rfl)
      rw [length_eq m h1, length_eq m' (hq ▸ h1), ← hq, hw]
  apply List.ext_getElem hlen
  intro j hj hj'
  have hi : j / 16 + 1 ≤ numChunks m := by unfold numChunks; omega
  have e := chunk_digit m j hj
  rw [hc _ (by omega) hi, chunk_digit m' j (hlen ▸ hj)] at e
  unfold byteAt at e
  rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ (hlen ▸ hj)] at e
  exact Fin.ext e.symm

theorem coeff_poly (m : Message) (k : ℕ) :
    (poly m).coeff k =
      if 1 ≤ k ∧ k ≤ numChunks m then (chunk m (numChunks m + 1 - k) : ℤ) else 0 := by
  unfold poly
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  split_ifs with hk
  · rw [show (Finset.Icc 1 (numChunks m)).filter (fun i => k = numChunks m + 1 - i) =
        {numChunks m + 1 - k} by
        ext i; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]; omega]
    simp
  · rw [show (Finset.Icc 1 (numChunks m)).filter (fun i => k = numChunks m + 1 - i) = ∅ by
        ext i; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty, iff_false]
        omega]
    simp

theorem coeff_poly_bounds (m : Message) (k : ℕ) :
    0 ≤ (poly m).coeff k ∧ (poly m).coeff k ≤ 2 ^ 129 := by
  rw [coeff_poly]
  split_ifs with hk
  · have := chunk_mem_Icc m (numChunks m + 1 - k) (by omega) (by omega)
    constructor
    · positivity
    · exact_mod_cast this.2
  · norm_num

theorem theorem_3_2_dev (m m' : Message) (u : ℤ)
    (h : (poly m' - poly m - Polynomial.C u).map (Int.castRingHom (ZMod p1305)) = 0) :
    m = m' := by
  have hcoef : ∀ k, 1 ≤ k → (poly m).coeff k = (poly m').coeff k := by
    intro k hk
    have := congrArg (fun P => P.coeff k) h
    simp only [coeff_map, coeff_sub, coeff_C, coeff_zero] at this
    rw [if_neg (by omega), sub_zero] at this
    have hd : (p1305 : ℤ) ∣ (poly m').coeff k - (poly m).coeff k := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p1305).mp
      simpa using this
    have b1 := coeff_poly_bounds m k
    have b2 := coeff_poly_bounds m' k
    have hp : (p1305 : ℤ) = 2 ^ 130 - 5 := by unfold p1305; norm_num
    have := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt, hp]; constructor <;> linarith)
    linarith
  have hq : numChunks m = numChunks m' := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have e := hcoef (numChunks m') (by omega)
      rw [coeff_poly, coeff_poly, if_neg (by omega), if_pos (by omega)] at e
      have := (chunk_mem_Icc m' (numChunks m' + 1 - numChunks m') (by omega) (by omega)).1
      omega
    · have e := hcoef (numChunks m) (by omega)
      rw [coeff_poly, coeff_poly, if_pos (by omega), if_neg (by omega)] at e
      have := (chunk_mem_Icc m (numChunks m + 1 - numChunks m) (by omega) (by omega)).1
      omega
  apply eq_of_chunks m m' hq
  intro i hi1 hi2
  have e := hcoef (numChunks m + 1 - i) (by omega)
  rw [coeff_poly, coeff_poly, if_pos (by omega), if_pos (by omega)] at e
  rw [← hq, show numChunks m + 1 - (numChunks m + 1 - i) = i by omega] at e
  exact_mod_cast e

end Poly1305.HashThm32

end
end

section
open Poly1305

theorem solution (m m' : Message) (u : ℤ)
    (h : (poly m' - poly m - Polynomial.C u).map (Int.castRingHom (ZMod p1305)) = 0) :
    m = m' := by
  apply Poly1305.HashThm32.theorem_3_2_dev <;> assumption

end
