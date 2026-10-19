-- Prove2me | solution 1 for ShorWiki.mulModGate_mulVec_eigState
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T03:45:44.816448+00:00
-- url     : https://prove2.me/submissions/4cac58bb-90af-4b31-b88e-5028d3c4aaa2

import Mathlib
import Definitions.Def_ShorWiki_Defs
open ShorWiki

namespace ShorGate

/-- The basis permutation underlying `mulModGate`. -/
def sig (N a n : ℕ) (hN : N ≤ 2 ^ n) (k : Fin (2 ^ n)) : Fin (2 ^ n) :=
  if h : (k : ℕ) < N then ⟨a * k % N, lt_of_lt_of_le (Nat.mod_lt _ (by omega)) hN⟩ else k

lemma sig_lt (N a n : ℕ) (hN : N ≤ 2 ^ n) (k : Fin (2 ^ n)) (hk : (k : ℕ) < N) :
    ((sig N a n hN k : Fin (2 ^ n)) : ℕ) = a * k % N := by
  unfold sig; rw [dif_pos hk]

lemma sig_ge (N a n : ℕ) (hN : N ≤ 2 ^ n) (k : Fin (2 ^ n)) (hk : N ≤ (k : ℕ)) :
    sig N a n hN k = k := by
  unfold sig; rw [dif_neg (by omega)]

lemma gate_eq (N a n : ℕ) (hN : N ≤ 2 ^ n) (i k : Fin (2 ^ n)) :
    mulModGate N a n i k = if i = sig N a n hN k then 1 else 0 := by
  unfold mulModGate sig
  split_ifs <;> simp_all [Fin.ext_iff]

lemma gate_pow (N a n : ℕ) (hN : N ≤ 2 ^ n) (m : ℕ) (i k : Fin (2 ^ n)) :
    (mulModGate N a n ^ m) i k = if i = (sig N a n hN)^[m] k then 1 else 0 := by
  induction m generalizing i with
  | zero => rw [pow_zero, Matrix.one_apply]; rfl
  | succ m ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp only [gate_eq N a n hN, ih]
    rw [Finset.sum_eq_single ((sig N a n hN)^[m] k)]
    · rw [Function.iterate_succ_apply']; simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ _) h

lemma iterate_sig (N a n : ℕ) (hN : N ≤ 2 ^ n) (m : ℕ) (k : Fin (2 ^ n)) (hk : (k : ℕ) < N) :
    (((sig N a n hN)^[m] k : Fin (2 ^ n)) : ℕ) = a ^ m * k % N := by
  induction m with
  | zero => simp [Nat.mod_eq_of_lt hk]
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    have hlt : (((sig N a n hN)^[m] k : Fin (2 ^ n)) : ℕ) < N := by
      rw [ih]; exact Nat.mod_lt _ (by omega)
    rw [sig_lt N a n hN _ hlt, ih, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, pow_succ]; ring_nf

lemma iterate_sig_ge (N a n : ℕ) (hN : N ≤ 2 ^ n) (m : ℕ) (k : Fin (2 ^ n)) (hk : N ≤ (k : ℕ)) :
    (sig N a n hN)^[m] k = k := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, sig_ge N a n hN k hk]

theorem gate_pow_ord (N a : ℕ) (ha : 1 < a) (haN : a < N) :
    mulModGate N a (regBits N) ^ ord N a = 1 := by
  have hN : N ≤ 2 ^ regBits N := Nat.le_pow_clog (by norm_num) N
  have hpow : a ^ ord N a % N = 1 := by
    have h := pow_orderOf_eq_one (a : ZMod N)
    rw [← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff'] at h
    unfold ord; rw [h, Nat.mod_eq_of_lt (by omega)]
  ext i k
  rw [gate_pow N a _ hN, Matrix.one_apply]
  congr 1
  apply propext
  suffices hfix : (sig N a (regBits N) hN)^[ord N a] k = k by rw [hfix]
  by_cases hk : (k : ℕ) < N
  · apply Fin.ext
    rw [iterate_sig N a _ hN _ k hk, Nat.mul_mod, hpow, one_mul, Nat.mod_mod,
      Nat.mod_eq_of_lt hk]
  · exact iterate_sig_ge N a _ hN _ k (by omega)

end ShorGate

namespace ShorGate

lemma ord_pos (N a : ℕ) (haN : a < N) (hcop : Nat.Coprime a N) : 0 < ord N a := by
  have : NeZero N := ⟨by omega⟩
  unfold ord
  have : orderOf (ZMod.unitOfCoprime a hcop) = orderOf (a : ZMod N) := by
    rw [← orderOf_units]; rfl
  rw [← this]
  exact orderOf_pos _

lemma pow_mod_ne_one (N a k : ℕ) (hk0 : 0 < k) (hk : k < ord N a) (hN : 1 < N) :
    a ^ k % N ≠ 1 := by
  intro h
  have h' : ((a ^ k : ℕ) : ZMod N) = ((1 : ℕ) : ZMod N) := by
    rw [ZMod.natCast_eq_natCast_iff', h, Nat.mod_eq_of_lt hN]
  push_cast at h'
  have := orderOf_dvd_of_pow_eq_one h'
  have := Nat.le_of_dvd hk0 this
  unfold ord at hk; omega

end ShorGate

open Matrix

open ShorGate in
theorem solution (N a : ℕ) (ha : 1 < a) (haN : a < N)
    (hcop : Nat.Coprime a N) (j : ℕ) :
    eigState N a (regBits N) j ≠ 0 ∧
      mulModGate N a (regBits N) *ᵥ eigState N a (regBits N) j
        = omega (ord N a) ^ j • eigState N a (regBits N) j := by
  have hN : N ≤ 2 ^ regBits N := Nat.le_pow_clog (by norm_num) N
  set r := ord N a with hr
  have hr0 : 0 < r := ord_pos N a haN hcop
  have hprim : IsPrimitiveRoot (omega r) r := Complex.isPrimitiveRoot_exp r hr0.ne'
  have hω0 : omega r ≠ 0 := hprim.ne_zero hr0.ne'
  have hpow : a ^ r % N = 1 := by
    have h := pow_orderOf_eq_one (a : ZMod N)
    rw [← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff'] at h
    rw [hr]; unfold ord; rw [h, Nat.mod_eq_of_lt (by omega)]
  set c : ℂ := (1 / Real.sqrt r : ℂ) with hc
  have hc0 : c ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt r := Real.sqrt_pos.mpr (by exact_mod_cast hr0)
    rw [hc]; simp only [one_div, ne_eq, inv_eq_zero, Complex.ofReal_eq_zero]; exact this.ne'
  constructor
  · -- the component at index 1 equals c
    intro h0
    have h1 : 1 < 2 ^ regBits N := lt_of_lt_of_le (by omega) hN
    have := congrFun h0 ⟨1, h1⟩
    simp only [eigState, Pi.zero_apply, ← hr] at this
    rw [Finset.sum_eq_single 0] at this
    · simp only [zero_mul, pow_zero, inv_one, one_mul, Nat.mod_eq_of_lt (show 1 < N by omega),
        if_true] at this
      rw [← hc] at this
      simp at this
      exact hc0 (by simpa using this)
    · intro k hk hk0
      have := pow_mod_ne_one N a k (Nat.pos_of_ne_zero hk0) (Finset.mem_range.mp hk) (by omega)
      rw [if_neg (Ne.symm this), mul_zero]
    · intro h; exact absurd (Finset.mem_range.mpr hr0) h
  · funext i
    simp only [Matrix.mulVec, dotProduct, gate_eq N a _ hN, eigState, Pi.smul_apply, smul_eq_mul,
      ← hr]
    set f : ℕ → ℂ := fun k => (omega r ^ (k * j))⁻¹ * if (i : ℕ) = a ^ k % N then 1 else 0 with hf
    have hcol : ∀ k : ℕ, (∑ x : Fin (2 ^ regBits N),
        (if i = sig N a (regBits N) hN x then (1 : ℂ) else 0) *
          ((omega r ^ (k * j))⁻¹ * if (x : ℕ) = a ^ k % N then 1 else 0)) = omega r ^ j * f (k + 1) := by
      intro k
      have hm : a ^ k % N < 2 ^ regBits N := lt_of_lt_of_le (Nat.mod_lt _ (by omega)) hN
      rw [Finset.sum_eq_single ⟨a ^ k % N, hm⟩]
      · have hs : ((sig N a (regBits N) hN ⟨a ^ k % N, hm⟩ : Fin _) : ℕ) = a ^ (k + 1) % N := by
          rw [sig_lt N a _ hN _ (Nat.mod_lt _ (by omega))]
          simp only
          rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, pow_succ, mul_comm]
        have hw : (omega r ^ (k * j))⁻¹ = omega r ^ j * (omega r ^ ((k + 1) * j))⁻¹ := by
          rw [add_mul, one_mul, pow_add]; field_simp
        simp only [hf, if_true, mul_one, Fin.ext_iff, hs, hw]
        split_ifs <;> ring
      · intro b _ hb
        have : (b : ℕ) ≠ a ^ k % N := fun h => hb (Fin.ext h)
        rw [if_neg this]; ring
      · intro h; exact absurd (Finset.mem_univ _) h
    have lhs : (∑ x : Fin (2 ^ regBits N),
        (if i = sig N a (regBits N) hN x then (1 : ℂ) else 0) *
          (1 / ↑√↑r * ∑ k ∈ Finset.range r,
            (omega r ^ (k * j))⁻¹ * if (x : ℕ) = a ^ k % N then 1 else 0)) =
        1 / ↑√↑r * ∑ k ∈ Finset.range r, omega r ^ j * f (k + 1) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← hcol k, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
    rw [lhs, ← Finset.mul_sum]
    have hfr : f r = f 0 := by
      simp only [hf, zero_mul, pow_zero, inv_one, hpow, Nat.mod_eq_of_lt (show 1 < N by omega)]
      rw [pow_mul, hprim.pow_eq_one, one_pow, inv_one]
    have hshift : ∑ k ∈ Finset.range r, f (k + 1) = ∑ k ∈ Finset.range r, f k := by
      have h1 := Finset.sum_range_succ f r
      have h2 := Finset.sum_range_succ' f r
      rw [hfr] at h1
      linear_combination h1 - h2
    rw [hshift]
    ring
