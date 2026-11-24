-- Prove2me | solution 1 for Poly1305.gmpOut_eq_poly1305
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-24T08:05:01.95029+00:00
-- url     : https://prove2.me/submissions/bfba8f38-38eb-4950-9aa5-78c83d2068a8

import Definitions.Def_Poly1305Bernstein
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.ModEq

section
section
namespace Poly1305.DefsGmp

/-- The polynomial value `c_1 R^q + ⋯ + c_q R`. -/
def P (R : ℕ) (m : Message) : ℕ :=
  ∑ i ∈ Finset.Icc 1 (numChunks m), chunk m i * R ^ (numChunks m + 1 - i)

theorem sum_Icc_eq_range (g : ℕ → ℕ) (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, g i = ∑ k ∈ Finset.range n, g (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

theorem numChunks_of_ne_nil (m : Message) (hm : m ≠ []) :
    numChunks m = numChunks (m.drop 16) + 1 := by
  have : 0 < m.length := List.length_pos_of_ne_nil hm
  unfold numChunks
  rw [List.length_drop]
  omega

theorem byteAt_drop (m : Message) (k : ℕ) : byteAt (m.drop 16) k = byteAt m (16 + k) := by
  unfold byteAt
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem byteAt_take (m : Message) (k : ℕ) (hk : k < 16) :
    byteAt (m.take 16) k = byteAt m k := by
  unfold byteAt
  simp [List.getD_eq_getElem?_getD, hk]

theorem chunk_succ (m : Message) (i : ℕ) (hi : 1 ≤ i) (h16 : 16 ≤ m.length) :
    chunk m (i + 1) = chunk (m.drop 16) i := by
  unfold chunk
  rw [List.length_drop]
  have e1 : (i + 1 ≤ m.length / 16) ↔ (i ≤ (m.length - 16) / 16) := by omega
  have e2 : (m.length - 16) % 16 = m.length % 16 := by omega
  rw [e2]
  have e3 : ∀ j, byteAt m (16 * (i + 1) - 16 + j) = byteAt (m.drop 16) (16 * i - 16 + j) := by
    intro j
    rw [byteAt_drop]
    congr 1
    omega
  simp only [e3]
  by_cases h : i ≤ (m.length - 16) / 16
  · rw [if_pos (e1.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (e1.mp h')), if_neg h]

theorem chunk_one (m : Message) (hm : m ≠ []) :
    chunk m 1 = (∑ j ∈ Finset.range (m.take 16).length, 2 ^ (8 * j) * byteAt (m.take 16) j) +
      2 ^ (8 * (m.take 16).length) := by
  have hpos : 0 < m.length := List.length_pos_of_ne_nil hm
  unfold chunk
  rw [List.length_take]
  have e : ∀ j ∈ Finset.range (min 16 m.length),
      2 ^ (8 * j) * byteAt m (16 * 1 - 16 + j) = 2 ^ (8 * j) * byteAt (m.take 16) j := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [show 16 * 1 - 16 + j = j by omega, byteAt_take m j (by omega)]
  by_cases h : 1 ≤ m.length / 16
  · rw [if_pos h]
    have : min 16 m.length = 16 := by omega
    rw [this] at e ⊢
    rw [Finset.sum_congr rfl e]
  · rw [if_neg h]
    have : min 16 m.length = m.length % 16 := by omega
    rw [this] at e ⊢
    rw [Finset.sum_congr rfl e]

theorem P_nil (R : ℕ) : P R [] = 0 := by
  simp [P, numChunks]

theorem P_cons (R : ℕ) (m : Message) (hm : m ≠ []) :
    P R m = chunk m 1 * R ^ (numChunks (m.drop 16) + 1) + P R (m.drop 16) := by
  unfold P
  rw [numChunks_of_ne_nil m hm, sum_Icc_eq_range, sum_Icc_eq_range, Finset.sum_range_succ',
    add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have h16 : 16 ≤ m.length := by
    have : 0 < numChunks (m.drop 16) := by omega
    unfold numChunks at this
    rw [List.length_drop] at this
    omega
  rw [chunk_succ m (k + 1) (by omega) h16,
    show numChunks (m.drop 16) + 1 + 1 - (k + 1 + 1) = numChunks (m.drop 16) + 1 - (k + 1) by omega]

theorem gmpLoop_cons (R h : ℕ) (m : Message) (hm : m ≠ []) :
    gmpLoop R h m = gmpLoop R ((h + ((∑ j ∈ Finset.range (m.take 16).length,
      2 ^ (8 * j) * byteAt (m.take 16) j) + 2 ^ (8 * (m.take 16).length))) * R % p1305)
      (m.drop 16) := by
  cases m with
  | nil => exact absurd rfl hm
  | cons b bs => rw [gmpLoop]

theorem gmpLoop_lt (R : ℕ) : ∀ (n : ℕ) (m : Message), m.length ≤ n → m ≠ [] →
    ∀ h, gmpLoop R h m < p1305 := by
  intro n
  induction n with
  | zero => intro m hl hm; exact absurd (List.eq_nil_of_length_eq_zero (by omega)) hm
  | succ n ih =>
    intro m hl hm h
    rw [gmpLoop_cons R h m hm]
    by_cases hd : m.drop 16 = []
    · rw [hd, gmpLoop]
      exact Nat.mod_lt _ (by unfold p1305; norm_num)
    · apply ih _ _ hd
      have : 0 < m.length := List.length_pos_of_ne_nil hm
      rw [List.length_drop]; omega

theorem gmpLoop_modEq (R : ℕ) : ∀ (n : ℕ) (m : Message), m.length ≤ n →
    ∀ h, gmpLoop R h m ≡ h * R ^ numChunks m + P R m [MOD p1305] := by
  intro n
  induction n with
  | zero =>
    intro m hl h
    have : m = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp [gmpLoop, P_nil, numChunks]
    rfl
  | succ n ih =>
    intro m hl h
    by_cases hm : m = []
    · subst hm
      simp [gmpLoop, P_nil, numChunks]
      rfl
    have hlen : (m.drop 16).length ≤ n := by
      have : 0 < m.length := List.length_pos_of_ne_nil hm
      rw [List.length_drop]; omega
    rw [gmpLoop_cons R h m hm, P_cons R m hm, numChunks_of_ne_nil m hm, ← chunk_one m hm]
    refine (ih _ hlen _).trans ?_
    have := Nat.mod_modEq ((h + chunk m 1) * R) p1305
    calc (h + chunk m 1) * R % p1305 * R ^ numChunks (m.drop 16) + P R (m.drop 16)
        ≡ (h + chunk m 1) * R * R ^ numChunks (m.drop 16) + P R (m.drop 16) [MOD p1305] :=
          Nat.ModEq.add_right _ (Nat.ModEq.mul_right _ this)
      _ = h * R ^ (numChunks (m.drop 16) + 1) +
            (chunk m 1 * R ^ (numChunks (m.drop 16) + 1) + P R (m.drop 16)) := by ring
      _ ≡ _ [MOD p1305] := Nat.ModEq.refl _

theorem gmpLoop_zero (R : ℕ) (m : Message) : gmpLoop R 0 m = P R m % p1305 := by
  by_cases hm : m = []
  · subst hm; simp [gmpLoop, P_nil]
  · have h1 := gmpLoop_modEq R m.length m le_rfl 0
    have h2 := gmpLoop_lt R m.length m le_rfl hm 0
    simp only [zero_mul, zero_add] at h1
    rw [← h1, Nat.mod_eq_of_lt h2]

theorem digit_mod (n : ℕ) (j : Fin 16) :
    n % 2 ^ 128 / 2 ^ (8 * (j : ℕ)) % 256 = n / 2 ^ (8 * (j : ℕ)) % 256 := by
  have hj := j.isLt
  have e : (2 : ℕ) ^ 128 = 2 ^ (8 * (j : ℕ)) * 2 ^ (128 - 8 * (j : ℕ)) := by
    rw [← pow_add]; congr 1; omega
  rw [e, Nat.mod_mul_right_div_self]
  apply Nat.mod_mod_of_dvd
  have : (256 : ℕ) = 2 ^ 8 := by norm_num
  rw [this]
  exact Nat.pow_dvd_pow 2 (by omega)

end Poly1305.DefsGmp

namespace Poly1305

theorem gmpOut_eq_poly1305_dev (r s : Str16) (m : Message) :
    gmpOut r s m = poly1305 (leVal r) m s := by
  have key := DefsGmp.gmpLoop_zero (leVal r) m
  have e : poly1305 (leVal r) m s =
      toStr16 ((DefsGmp.P (leVal r) m % p1305 + leVal s) % 2 ^ 128) := by
    unfold poly1305 DefsGmp.P
    rfl
  rw [e]
  funext j
  apply Fin.ext
  simp only [gmpOut, toStr16, key]
  exact (DefsGmp.digit_mod _ j).symm

end Poly1305

end
end

section
open Poly1305

theorem solution (r s : Str16) (m : Message) :
    gmpOut r s m = poly1305 (leVal r) m s := by
  apply Poly1305.gmpOut_eq_poly1305_dev <;> assumption

end
