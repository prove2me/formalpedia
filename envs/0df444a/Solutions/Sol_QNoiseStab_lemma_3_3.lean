-- Prove2me | solution 1 for QNoiseStab.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @blake-holman
-- created : 2026-11-26T04:04:13.480916+00:00
-- url     : https://prove2.me/submissions/03dd9d20-c646-4d0f-a780-850a2cdbe770

import Mathlib
import Definitions.Def_QNoiseStab_projLowDeg
import Definitions.Def_QNoiseStab_noiseOp

-- Solutions.Lemma33
section
open scoped ComplexOrder

namespace QNoiseStab

/-- **Lemma 3.3** (Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query Complexity
and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…),
p.12). For `A ⊆ [n]`, `0 ≤ p < 1`, and every nonnegative integer `t`,
`Π_{B_t} ⪯ (1 − p)^{-t} T_p^A`.

**Formalization Note** The Loewner order `P ⪯ Q` is `(Q − P).PosSemidef`. `(1 − p)^{-t}` is
`((1 − p)^t)⁻¹` (positive since `p < 1`). `t` ranges over all of `ℕ`, including `t > n`. -/
private theorem submission_proof {n m : ℕ} [NeZero m] (A : Finset (Fin n)) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1)
    (t : ℕ) :
    Matrix.PosSemidef (((((1 - p) ^ t)⁻¹ : ℝ) : ℂ) • (noiseOp p A : Matrix (Fin n → ZMod m)
      (Fin n → ZMod m) ℂ) - projLowDeg t) := by
  classical
  have hpos : 0 < 1 - p := sub_pos.mpr hp1
  have hunit : 1 - p ≤ 1 := by linarith
  unfold noiseOp projLowDeg
  rw [Finset.smul_sum, Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Matrix.posSemidef_sum
  intro z _
  have hket : (ketBra (fourierVec z)).PosSemidef :=
    Matrix.posSemidef_vecMulVec_self_star (fun x => fourierVec z x)
  rw [smul_smul]
  by_cases hz : fourierWeight z ≤ t
  · have hcount : (A.filter fun i => z i ≠ 0).card ≤ fourierWeight z :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ A))
    have hpow := pow_le_pow_of_le_one hpos.le hunit (hcount.trans hz)
    have hscale : 1 ≤ ((1 - p) ^ t)⁻¹ * (1 - p) ^ (A.filter fun i => z i ≠ 0).card := by
      rw [← div_eq_inv_mul, le_div_iff₀ (pow_pos hpos t), one_mul]
      exact hpow
    rw [if_pos hz, ← one_smul ℂ (ketBra (fourierVec z))]
    -- Combine the scalar coefficients of this rank-one matrix.
    simp only [smul_smul, mul_one, ← sub_smul]
    apply hket.smul
    exact_mod_cast sub_nonneg.mpr hscale
  · rw [if_neg hz, sub_zero]
    apply hket.smul
    exact_mod_cast mul_nonneg (inv_nonneg.mpr (pow_nonneg hpos.le t)) (pow_nonneg hpos.le _)

end QNoiseStab
end

section
open scoped ComplexOrder
open QNoiseStab

set_option linter.unusedVariables false in
theorem solution :
    ∀ {n m : ℕ} [NeZero m] (A : Finset (Fin n)) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1)
        (t : ℕ),
      Matrix.PosSemidef (((((1 - p) ^ t)⁻¹ : ℝ) : ℂ) • (noiseOp p A : Matrix (Fin n → ZMod m)
        (Fin n → ZMod m) ℂ) - projLowDeg t) :=
  @QNoiseStab.submission_proof

end
