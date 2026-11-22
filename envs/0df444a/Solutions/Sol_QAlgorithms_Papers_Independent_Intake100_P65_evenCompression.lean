-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P65.evenCompression
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-21T09:04:01.278474+00:00
-- url     : https://prove2.me/submissions/2436ac76-f343-4e6f-b17e-841a77d0614d

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P65

noncomputable section

open scoped BigOperators TensorProduct

open QAlgorithms.Papers.Independent.Renew46.P16

open QAlgorithms.Papers.Independent.Support21.P08 (IrreducibleRepresentation)

open QAlgorithms.Papers.Independent.Support21.P12

open QAlgorithms.Papers.Independent.Support21.P14 (BrauerPairing oddPairingCount)

namespace QAlgorithms.Papers.Independent.Intake100.P65

universe u v

theorem evenCompression (R : Type u) [CommRing R] [Invertible (2 : R)]
    (omega : ℕ → R) (n : ℕ) (hn : 2 ≤ n) (a : ℕ) (ha : 0 < a) :
    (0 : AffineBMW R omega n) =
      (∑ b ∈ Finset.range (2*a), (-1 : R)^b * omega b * omega (2*a-1-b)) •
        affineE R omega n 0 := by
  have key : ∑ b ∈ Finset.range (2*a), (-1 : R)^b * omega b * omega (2*a-1-b) = 0 := by
    set S := ∑ b ∈ Finset.range (2*a), (-1 : R)^b * omega b * omega (2*a-1-b) with hS
    have h2 : S = -S := by
      conv_lhs => rw [hS, ← Finset.sum_range_reflect]
      rw [hS, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun b hb => ?_
      have hb' := Finset.mem_range.mp hb
      have e1 : 2*a-1-(2*a-1-b) = b := by omega
      rw [e1]
      have e2 : (-1 : R)^(2*a-1-b) = -(-1 : R)^b := by
        have : (-1 : R)^(2*a-1-b) * (-1)^b = -1 := by
          rw [← pow_add]
          have : 2*a-1-b+b = 2*(a-1)+1 := by omega
          rw [this, pow_succ, pow_mul]; simp
        have hu : (-1 : R)^b * (-1)^b = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
        calc (-1 : R)^(2*a-1-b) = (-1 : R)^(2*a-1-b) * ((-1)^b * (-1)^b) := by rw [hu, mul_one]
          _ = -(-1 : R)^b := by rw [← mul_assoc, this]; ring
      rw [e2]; ring
    have : (2 : R) * S = 0 := by linear_combination h2
    have := congrArg (fun x => ⅟(2:R) * x) this
    simpa [← mul_assoc] using this
  rw [key, zero_smul]

end QAlgorithms.Papers.Independent.Intake100.P65

end

theorem solution (R : Type*) [CommRing R] [Invertible (2 : R)]
    (omega : ℕ → R) (n : ℕ) (hn : 2 ≤ n) (a : ℕ) (ha : 0 < a) :
    (0 : QAlgorithms.Papers.Independent.Renew46.P16.AffineBMW R omega n) =
      (∑ b ∈ Finset.range (2*a), (-1 : R)^b * omega b * omega (2*a-1-b)) •
        QAlgorithms.Papers.Independent.Renew46.P16.affineE R omega n 0 :=
  QAlgorithms.Papers.Independent.Intake100.P65.evenCompression R omega n hn a ha
