-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P16.degenerateAffine_skein_power
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T00:09:59.440617+00:00
-- url     : https://prove2.me/submissions/02a2b371-8093-41b0-a4e4-0bc112ed20a4

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P16
noncomputable section

open scoped BigOperators

open QAlgorithms.Papers.Independent.Renew46.P16

theorem g64j_skein_gen {A : Type*} [Ring A] (s X Y e : A) (h : s * X - Y * s = e - 1) (a : ℕ) :
    s * X ^ a = Y ^ a * s + ∑ b ∈ Finset.Icc 1 a, Y ^ (b - 1) * (e - 1) * X ^ (a - b) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Finset.sum_Icc_succ_top (by omega), pow_succ, ← mul_assoc, ih]
    have hsum : ∑ b ∈ Finset.Icc 1 a, Y ^ (b - 1) * (e - 1) * X ^ (a + 1 - b) =
        (∑ b ∈ Finset.Icc 1 a, Y ^ (b - 1) * (e - 1) * X ^ (a - b)) * X := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun b hb => ?_)
      have hb' : b ≤ a := (Finset.mem_Icc.1 hb).2
      rw [show a + 1 - b = (a - b) + 1 by omega, pow_succ, mul_assoc _ _ X]
    rw [hsum, show a + 1 - 1 = a by omega, Nat.sub_self, pow_zero, mul_one, add_mul,
      mul_assoc (Y ^ a) s X]
    have h' : s * X = Y * s + (e - 1) := by rw [← h]; abel
    rw [h', pow_succ]
    noncomm_ring

theorem solution (S : Type*) [CommRing S] (omega : ℕ → S)
    (n i a : ℕ) (hi : i + 1 < n) (ha : 1 ≤ a) :
    affineS S omega n i * affineX S omega n i ^ a =
      affineX S omega n (i + 1) ^ a * affineS S omega n i +
        ∑ b ∈ Finset.Icc 1 a,
          affineX S omega n (i + 1) ^ (b - 1) *
            (affineE S omega n i - 1) * affineX S omega n i ^ (a - b) := by
  apply g64j_skein_gen
  have h := RingQuot.mkAlgHom_rel S (BMWRel.skeinLeft (S := S) (omega := omega) (n := n) i hi)
  simpa only [affineS, affineX, affineE, affineBMWQuotientMap, map_sub, map_mul, map_one] using h
