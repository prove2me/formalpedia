-- Prove2me | solution 1 for QAPooling.MaxMin.profit_identity
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T09:41:58.496189+00:00
-- url     : https://prove2.me/submissions/ebc0032a-ad3c-476e-9c39-c931ba3348d2

import Mathlib
import Definitions.Def_QAPooling_MaxMin_Model

namespace QAPooling.MaxMin.ProfitProof

lemma exposure_score {n : ℕ} {s : ScoringRule n} {g : (Fin n → ℝ) → Fin n → ℝ}
    (hg : IsExposure s g) {p : Fin n → ℝ} (hp : p ∈ forecastDomain s) (j : Fin n) :
    s p j = ((expectedReward s p + g p j - ∑ k, g p k * p k : ℝ) : EReal) := by
  rw [hg p hp j]
  congr 1
  simp [mul_sub, Finset.sum_sub_distrib, Pi.single_apply, mul_ite]
  ring

end QAPooling.MaxMin.ProfitProof

open QAPooling.MaxMin QAPooling.MaxMin.ProfitProof

theorem solution {n m : ℕ} (s : ScoringRule n) (g : (Fin n → ℝ) → Fin n → ℝ)
    (hg : IsExposure s g)
    (p : Fin m → Fin n → ℝ) (hp : ∀ i, p i ∈ forecastDomain s)
    (w : Fin m → ℝ) (hw1 : ∑ i, w i = 1)
    (pstar : Fin n → ℝ) (hD : pstar ∈ forecastDomain s)
    (lam : ℝ) (mu : Fin n → ℝ)
    (hkkt : ∀ j, g pstar j = ∑ i, w i * g (p i) j + lam + mu j)
    (hcs : ∀ j, 0 < pstar j → mu j = 0) :
    ∀ j, profit s p w pstar j = ((∑ i, w i * bregman s g pstar (p i) + mu j : ℝ) : EReal) := by
  have hmu : ∑ j, mu j * pstar j = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : 0 < pstar j
    · rw [hcs j hj, zero_mul]
    · have hz : pstar j = 0 := le_antisymm (le_of_not_gt hj) (hD.1.1 j)
      rw [hz, mul_zero]
  have hsum : ∑ j, (∑ i, w i * g (p i) j) * pstar j =
      ∑ i, w i * ∑ j, g (p i) j * pstar j := by
    simp_rw [Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  have hdot : ∑ j, g pstar j * pstar j =
      (∑ i, w i * ∑ j, g (p i) j * pstar j) + lam := by
    simp_rw [hkkt, add_mul]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsum, hmu,
      ← Finset.mul_sum, hD.1.2, mul_one, add_zero]
  intro j
  unfold profit
  rw [exposure_score hg hD j]
  simp_rw [exposure_score hg (hp _) j, EReal.toReal_coe]
  rw [← EReal.coe_sub]
  congr 1
  rw [hdot, hkkt j]
  have hconst : ∑ i, w i * expectedReward s pstar = expectedReward s pstar := by
    rw [← Finset.sum_mul, hw1, one_mul]
  simp only [bregman, mul_sub, Finset.sum_sub_distrib]
  rw [hconst]
  simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  ring
