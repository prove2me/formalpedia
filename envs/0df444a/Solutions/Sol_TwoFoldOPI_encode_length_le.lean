-- Prove2me | solution 1 for TwoFoldOPI.encode_length_le
-- status  : ACCEPTED   (prove)
-- author  : @sragavan
-- created : 2026-11-10T20:18:41.011125+00:00
-- url     : https://prove2.me/submissions/b136fa8f-df7a-41ba-8004-9f6566026022

import Mathlib
import Definitions.Def_TwoFoldOPI_Input

open TwoFoldOPI

private lemma encBin_length_le (n : ℕ) : (QAlgorithms.LocalHamiltonian.encBin n).length ≤ 2 * n + 2 := by
  unfold QAlgorithms.LocalHamiltonian.encBin
  rw [List.length_append, List.length_flatMap]
  have h1 : (List.map (fun β : Bool => [true, β].length) n.bits).sum = 2 * n.bits.length := by
    simp [List.sum_replicate, mul_comm]
  have h2 : n.bits.length ≤ n := by
    rw [Nat.size_eq_bits_len, Nat.size_le]
    exact Nat.lt_two_pow_self
  simp only [List.length_cons, List.length_nil] at h1 ⊢
  omega

theorem solution : ∃ a b : ℕ, ∀ x : Input, x.encode.length ≤ a * (x.scale + 1) ^ b := by
  refine ⟨40, 4, fun x => ?_⟩
  -- basic quantities
  set S := x.scale + 1 with hS
  have hp2 : 2 ≤ x.F.p := x.F.hp.two_le
  have he1 : 1 ≤ x.F.f.natDegree := by
    have := (Polynomial.Monic.natDegree_pos x.F.hmonic).mpr (fun h1 => x.F.hirr.not_isUnit (by
      rw [h1]; exact isUnit_one))
    omega
  have hq : x.F.q = x.F.p ^ x.F.f.natDegree := rfl
  have hpq : x.F.p ≤ x.F.q := by
    rw [hq]; calc x.F.p = x.F.p ^ 1 := (pow_one x.F.p).symm
      _ ≤ x.F.p ^ x.F.f.natDegree := Nat.pow_le_pow_right (by omega) he1
  have heq : x.F.f.natDegree + 1 ≤ x.F.q := by
    rw [hq]
    calc x.F.f.natDegree + 1 ≤ 2 ^ x.F.f.natDegree := Nat.lt_two_pow_self
      _ ≤ x.F.p ^ x.F.f.natDegree := Nat.pow_le_pow_left hp2 x.F.f.natDegree
  have hscale : x.scale = x.m + x.r + x.F.q + x.t := rfl
  have hclog : Nat.clog 2 x.F.p ≤ x.F.p := by
    rw [Nat.clog_le_iff_le_pow (by norm_num)]
    exact (Nat.lt_two_pow_self).le
  have hb : bitsPerSymbol x.F ≤ x.F.f.natDegree * x.F.p := Nat.mul_le_mul_left _ hclog
  -- length of the field description
  have hcoef : ∀ j : Fin (x.F.f.natDegree + 1), (x.F.f.coeff j).val ≤ x.F.p := by
    intro j
    have : NeZero x.F.p := ⟨by omega⟩
    exact (ZMod.val_lt _).le
  have hfield : (fieldEncode x.F).length ≤ (2 * x.F.p + 2) + (2 * x.F.f.natDegree + 2) + (x.F.f.natDegree + 1) * (2 * x.F.p + 2) := by
    unfold fieldEncode
    simp only [List.length_append, List.length_flatten, List.map_ofFn, List.sum_ofFn]
    have h1 := encBin_length_le x.F.p
    have h2 := encBin_length_le x.F.f.natDegree
    have h3 : ∑ j : Fin (x.F.f.natDegree + 1),
        (Function.comp List.length (fun j : Fin (x.F.f.natDegree + 1) =>
          QAlgorithms.LocalHamiltonian.encBin (x.F.f.coeff j).val)) j ≤ (x.F.f.natDegree + 1) * (2 * x.F.p + 2) := by
      calc ∑ j : Fin (x.F.f.natDegree + 1),
            (Function.comp List.length (fun j : Fin (x.F.f.natDegree + 1) =>
              QAlgorithms.LocalHamiltonian.encBin (x.F.f.coeff j).val)) j
          ≤ ∑ _j : Fin (x.F.f.natDegree + 1), (2 * x.F.p + 2) := by
            apply Finset.sum_le_sum; intro j _
            simp only [Function.comp]
            exact (encBin_length_le _).trans (by have := hcoef j; omega)
        _ = (x.F.f.natDegree + 1) * (2 * x.F.p + 2) := by simp
    omega
  -- the full encoding
  have hlen : x.encode.length = (fieldEncode x.F).length +
      (QAlgorithms.LocalHamiltonian.encBin x.m).length +
      (QAlgorithms.LocalHamiltonian.encBin x.r).length + 1 +
      x.r * (x.m * bitsPerSymbol x.F) + x.m * bitsPerSymbol x.F +
      (QAlgorithms.LocalHamiltonian.encBin x.t).length := by
    unfold Input.encode
    simp only [List.length_append, List.length_flatten, List.map_ofFn, List.sum_ofFn,
      List.length_singleton, Function.comp_def, List.length_ofFn, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hm := encBin_length_le x.m
  have hr := encBin_length_le x.r
  have ht := encBin_length_le x.t
  rw [hlen]
  -- crude bounds in terms of S
  have hpS : x.F.p ≤ S := by omega
  have heS : x.F.f.natDegree + 1 ≤ S := by omega
  have hmS : x.m + 1 ≤ S := by omega
  have hrS : x.r + 1 ≤ S := by omega
  have htS : x.t + 1 ≤ S := by omega
  have hS1 : 1 ≤ S := by omega
  have hrmb : x.r * (x.m * bitsPerSymbol x.F) ≤ S ^ 4 := by
    calc x.r * (x.m * bitsPerSymbol x.F) ≤ S * (S * (S * S)) := by
          apply Nat.mul_le_mul (by omega)
          apply Nat.mul_le_mul (by omega)
          exact hb.trans (Nat.mul_le_mul (by omega) hpS)
      _ = S ^ 4 := by ring
  have hmb : x.m * bitsPerSymbol x.F ≤ S ^ 4 := by
    calc x.m * bitsPerSymbol x.F ≤ S * (S * S) := by
          apply Nat.mul_le_mul (by omega)
          exact hb.trans (Nat.mul_le_mul (by omega) hpS)
      _ = S * S * S * 1 := by ring
      _ ≤ S * S * S * S := Nat.mul_le_mul_left _ hS1
      _ = S ^ 4 := by ring
  have hS4 : S ≤ S ^ 4 := by
    calc S = S ^ 1 := (pow_one S).symm
      _ ≤ S ^ 4 := Nat.pow_le_pow_right hS1 (by norm_num)
  have hS2 : S * S ≤ S ^ 4 := by
    calc S * S = S ^ 2 := by ring
      _ ≤ S ^ 4 := Nat.pow_le_pow_right hS1 (by norm_num)
  have hep : (x.F.f.natDegree + 1) * (2 * x.F.p + 2) ≤ 4 * (S * S) := by
    calc (x.F.f.natDegree + 1) * (2 * x.F.p + 2) ≤ S * (2 * S + 2 * S) :=
          Nat.mul_le_mul heS (by omega)
      _ = 4 * (S * S) := by ring
  nlinarith
