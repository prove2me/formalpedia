-- Prove2me | solution 1 for ShorWiki.mulModGate_pow_ord
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T03:42:50.30599+00:00
-- url     : https://prove2.me/submissions/170b8028-6526-4963-90aa-ca816d9ab980

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

theorem solution (N a : ℕ) (ha : 1 < a) (haN : a < N)
    (hcop : Nat.Coprime a N) :
    mulModGate N a (regBits N) ^ ord N a = 1 :=
  ShorGate.gate_pow_ord N a ha haN
