-- Prove2me | solution 1 for SQMeanEstimation.ring_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:09:54.359789+00:00
-- url     : https://prove2.me/submissions/4470b425-9954-4486-ac20-1ec4fa93b710

import Mathlib
import Definitions.Def_SQMeanEstimation_posPart
import Definitions.Def_SQMeanEstimation_negPart
import Definitions.Def_SQMeanEstimation_ringPart
import Definitions.Def_SQMeanEstimation_ringInf

namespace Aux_SQMeanEstimation_ring_decomposition

theorem pow_lt (n : ℕ) : (2 : ℝ) ^ (-((n : ℝ) + 1)) < (2 : ℝ) ^ (-(n : ℝ)) :=
  Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)

theorem telescope {d : ℕ} (u : Fin d → ℝ) (i : Fin d) (hu : |u i| ≤ 1) : ∀ n : ℕ,
    (∑ j ∈ Finset.range n, SQMeanEstimation.ringPart j u i) +
      (if |u i| ≤ (2 : ℝ) ^ (-(n : ℝ)) then u i else 0) = u i := by
  intro n
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, neg_zero, Real.rpow_zero,
      zero_add]
    rw [if_pos hu]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hlt := pow_lt n
    have key : SQMeanEstimation.ringPart n u i +
        (if |u i| ≤ (2 : ℝ) ^ (-((n + 1 : ℕ) : ℝ)) then u i else 0)
        = (if |u i| ≤ (2 : ℝ) ^ (-(n : ℝ)) then u i else 0) := by
      rw [Nat.cast_add_one]
      simp only [SQMeanEstimation.ringPart]
      by_cases ha : |u i| ≤ (2 : ℝ) ^ (-((n : ℝ) + 1))
      · have hb : |u i| ≤ (2 : ℝ) ^ (-(n : ℝ)) := le_trans ha hlt.le
        have hc : ¬ ((2 : ℝ) ^ (-((n : ℝ) + 1)) < |u i| ∧ |u i| ≤ (2 : ℝ) ^ (-(n : ℝ))) :=
          fun h => absurd h.1 (not_lt.mpr ha)
        rw [if_neg hc, if_pos ha, if_pos hb, zero_add]
      · by_cases hb : |u i| ≤ (2 : ℝ) ^ (-(n : ℝ))
        · have hc : ((2 : ℝ) ^ (-((n : ℝ) + 1)) < |u i| ∧ |u i| ≤ (2 : ℝ) ^ (-(n : ℝ))) :=
            ⟨not_le.mp ha, hb⟩
          rw [if_pos hc, if_neg ha, if_pos hb, add_zero]
        · have hc : ¬ ((2 : ℝ) ^ (-((n : ℝ) + 1)) < |u i| ∧ |u i| ≤ (2 : ℝ) ^ (-(n : ℝ))) :=
            fun h => hb h.2
          rw [if_neg hc, if_neg ha, if_neg hb, add_zero]
    rw [add_assoc, key]
    exact ih

theorem inf_eq {d : ℕ} (k : ℤ) (u : Fin d → ℝ) (i : Fin d) (hu : |u i| ≤ 1) :
    SQMeanEstimation.ringInf k u i
      = if |u i| ≤ (2 : ℝ) ^ (-(((k + 1).toNat : ℕ) : ℝ)) then u i else 0 := by
  simp only [SQMeanEstimation.ringInf]
  by_cases hk : -1 ≤ k
  · have h1 : (((k + 1).toNat : ℕ) : ℤ) = k + 1 := by omega
    have hK : (((k + 1).toNat : ℕ) : ℝ) = (k : ℝ) + 1 := by
      have h2 : ((((k + 1).toNat : ℕ) : ℤ) : ℝ) = ((k + 1 : ℤ) : ℝ) := by rw [h1]
      rw [Int.cast_natCast, Int.cast_add, Int.cast_one] at h2
      exact h2
    have hexp : (2 : ℝ) ^ (-k - 1) = (2 : ℝ) ^ (-(((k + 1).toNat : ℕ) : ℝ)) := by
      rw [← Real.rpow_intCast, hK]
      congr 1
      rw [Int.cast_sub, Int.cast_neg, Int.cast_one]
      ring
    rw [hexp]
  · have h0 : (k + 1).toNat = 0 := by omega
    have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ (-k - 1) := one_le_zpow₀ (by norm_num) (by omega)
    rw [h0, if_pos (le_trans hu hpow)]
    simp only [Nat.cast_zero, neg_zero, Real.rpow_zero]
    rw [if_pos hu]

end Aux_SQMeanEstimation_ring_decomposition

open SQMeanEstimation in
theorem solution {d : ℕ} :
    (∀ (k : ℤ) (w : Fin d → ℝ), (∀ i, |w i| ≤ 1) →
      w = (∑ j ∈ Finset.range (k + 1).toNat,
          (ringPart j (SQMeanEstimation.posPart w) - ringPart j (SQMeanEstimation.negPart w)))
        + (ringInf k (SQMeanEstimation.posPart w) - ringInf k (SQMeanEstimation.negPart w))) ∧
    (∀ (w : Fin d → ℝ) (j : ℕ) (i : Fin d),
      0 ≤ (2 : ℝ) ^ j * ringPart j (SQMeanEstimation.posPart w) i ∧
        (2 : ℝ) ^ j * ringPart j (SQMeanEstimation.posPart w) i ≤ 1)
    := by
  refine ⟨?_, ?_⟩
  · intro k w hw
    funext i
    have hpi : |SQMeanEstimation.posPart w i| ≤ 1 := by
      simp only [SQMeanEstimation.posPart]
      split_ifs <;> simp [hw i]
    have hni : |SQMeanEstimation.negPart w i| ≤ 1 := by
      simp only [SQMeanEstimation.negPart]
      split_ifs <;> simp [hw i]
    have e1 := Aux_SQMeanEstimation_ring_decomposition.telescope
      (SQMeanEstimation.posPart w) i hpi ((k + 1).toNat)
    have e2 := Aux_SQMeanEstimation_ring_decomposition.telescope
      (SQMeanEstimation.negPart w) i hni ((k + 1).toNat)
    rw [← Aux_SQMeanEstimation_ring_decomposition.inf_eq k _ i hpi] at e1
    rw [← Aux_SQMeanEstimation_ring_decomposition.inf_eq k _ i hni] at e2
    have hx : SQMeanEstimation.posPart w i - SQMeanEstimation.negPart w i = w i := by
      simp only [SQMeanEstimation.posPart, SQMeanEstimation.negPart]
      split_ifs <;> linarith
    simp only [Pi.add_apply, Pi.sub_apply, Finset.sum_apply, Finset.sum_sub_distrib]
    linarith
  · intro w j i
    have hp0 : 0 ≤ SQMeanEstimation.posPart w i := by
      simp only [SQMeanEstimation.posPart]
      split_ifs with h
      · exact h
      · exact le_rfl
    have h2j : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    have hone : (2 : ℝ) ^ j * (2 : ℝ) ^ (-(j : ℝ)) = 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), add_neg_cancel,
        Real.rpow_zero]
    by_cases hc : (2 : ℝ) ^ (-((j : ℝ) + 1)) < |SQMeanEstimation.posPart w i| ∧
        |SQMeanEstimation.posPart w i| ≤ (2 : ℝ) ^ (-(j : ℝ))
    · have hv : ringPart j (SQMeanEstimation.posPart w) i = SQMeanEstimation.posPart w i := by
        simp only [ringPart]
        rw [if_pos hc]
      rw [hv]
      refine ⟨mul_nonneg h2j.le hp0, ?_⟩
      have hb := hc.2
      rw [abs_of_nonneg hp0] at hb
      calc (2 : ℝ) ^ j * SQMeanEstimation.posPart w i ≤ (2 : ℝ) ^ j * (2 : ℝ) ^ (-(j : ℝ)) :=
            mul_le_mul_of_nonneg_left hb h2j.le
        _ = 1 := hone
    · have hv : ringPart j (SQMeanEstimation.posPart w) i = 0 := by
        simp only [ringPart]
        rw [if_neg hc]
      rw [hv, mul_zero]
      exact ⟨le_rfl, zero_le_one⟩
