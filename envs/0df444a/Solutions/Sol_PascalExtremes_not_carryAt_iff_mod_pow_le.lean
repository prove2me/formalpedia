-- Prove2me | solution 1 for PascalExtremes.not_carryAt_iff_mod_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:55:10.506061+00:00
-- url     : https://prove2.me/submissions/ca25e546-d9b7-471e-a06a-dcbbf6b25b7c

module
public import Definitions.Def_PascalExtremes_Basic
public import Definitions.Def_PascalExtremes_Digits
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Definitions.Def_PascalExtremes_Kummer
public import Theorems.Thm_PascalExtremes_mem_admissibleIndices_iff
attribute [local simp] PascalExtremes.mem_admissibleIndices_iff



set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes
namespace PascalExtremes
theorem _root_.solution {p n k i : ℕ} (hp : 0 < p) (hkn : k ≤ n) :
    ¬ CarryAt p n k i ↔ k % p ^ i ≤ n % p ^ i := by
  unfold CarryAt
  have hpow : 0 < p ^ i := pow_pos hp i
  have hnmod :
      n % p ^ i =
        (k % p ^ i + (n - k) % p ^ i) % p ^ i := by
    calc
      n % p ^ i = (k + (n - k)) % p ^ i := by
        rw [Nat.add_sub_of_le hkn]
      _ = (k % p ^ i + (n - k) % p ^ i) % p ^ i :=
        Nat.add_mod _ _ _
  constructor
  · intro hnocarry
    have hsum :
        k % p ^ i + (n - k) % p ^ i < p ^ i :=
      Nat.lt_of_not_ge hnocarry
    have hnmod' :
        n % p ^ i = k % p ^ i + (n - k) % p ^ i := by
      calc
        n % p ^ i =
            (k % p ^ i + (n - k) % p ^ i) % p ^ i := hnmod
        _ = k % p ^ i + (n - k) % p ^ i := Nat.mod_eq_of_lt hsum
    rw [hnmod']
    exact Nat.le_add_right _ _
  · intro hkmod hcarry
    have hklt : k % p ^ i < p ^ i := Nat.mod_lt _ hpow
    have hrlt : (n - k) % p ^ i < p ^ i := Nat.mod_lt _ hpow
    have hsum_lt_double :
        k % p ^ i + (n - k) % p ^ i < p ^ i + p ^ i :=
      Nat.add_lt_add hklt hrlt
    have hsum_lt_pow_add_k :
        k % p ^ i + (n - k) % p ^ i < p ^ i + k % p ^ i := by
      simpa [Nat.add_comm] using Nat.add_lt_add_left hrlt (k % p ^ i)
    have hsub_lt_pow :
        (k % p ^ i + (n - k) % p ^ i) - p ^ i < p ^ i :=
      Nat.sub_lt_left_of_lt_add hcarry hsum_lt_double
    have hsub_lt_k :
        (k % p ^ i + (n - k) % p ^ i) - p ^ i < k % p ^ i :=
      Nat.sub_lt_left_of_lt_add hcarry hsum_lt_pow_add_k
    have hsum_mod :
        (k % p ^ i + (n - k) % p ^ i) % p ^ i =
          (k % p ^ i + (n - k) % p ^ i) - p ^ i := by
      rw [Nat.mod_eq_sub_mod hcarry, Nat.mod_eq_of_lt hsub_lt_pow]
    have hnmod' :
        n % p ^ i =
          (k % p ^ i + (n - k) % p ^ i) - p ^ i :=
      hnmod.trans hsum_mod
    rw [hnmod'] at hkmod
    exact (Nat.not_le_of_gt hsub_lt_k) hkmod
end PascalExtremes
