-- Prove2me | solution 1 for WeightedMajority.Continuous.theorem_5_2
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T00:37:49.755754+00:00
-- url     : https://prove2.me/submissions/0217b9b4-d07a-4abf-9b44-ec3734792868

import Definitions.Def_WeightedMajority_Continuous_WMCRun

open Finset WeightedMajority.Basic
open WeightedMajority.Continuous

namespace ContinuousProof

variable {n t : ℕ} {beta : ℝ} {w : ℕ → Fin n → ℝ}
  {x : Fin t → Fin n → ℝ} {rho : Fin t → ℝ}

lemma weight_nonneg (h : PotentialConditions beta w x rho) {k : ℕ} (hk : k ≤ t) :
    0 ≤ totalWeight w k :=
  Finset.sum_nonneg fun i _ => h.1.2.2.2.2.1 k hk i

lemma step (h : PotentialConditions beta w x rho) (j : Fin t)
    (hpos : 0 < totalWeight w j.val) :
    totalWeight w (j.val + 1) ≤ totalWeight w j.val *
      (1 - (1 - beta) * |meanPrediction w x j - rho j|) := by
  have hn := h.1.2.2.2.2.1 j.val (Nat.le_of_lt j.isLt)
  have hb : 0 ≤ 1 - beta := by linarith [h.1.2.2.1]
  have heq : (∑ i : Fin n, w j.val i * (x j i - rho j)) =
      totalWeight w j.val * (meanPrediction w x j - rho j) := by
    rw [show (∑ i : Fin n, w j.val i * (x j i - rho j)) =
      (∑ i : Fin n, w j.val i * x j i) - totalWeight w j.val * rho j by
        simp [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul, totalWeight]]
    unfold meanPrediction
    field_simp
  have habs : totalWeight w j.val * |meanPrediction w x j - rho j| ≤
      ∑ i : Fin n, w j.val i * |x j i - rho j| := by
    calc
      _ = |∑ i : Fin n, w j.val i * (x j i - rho j)| := by
        rw [heq, abs_mul, abs_of_pos hpos]
      _ ≤ ∑ i : Fin n, |w j.val i * (x j i - rho j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [abs_mul, abs_of_nonneg (hn i)]
  calc
    totalWeight w (j.val + 1) ≤
        ∑ i : Fin n, w j.val i * (1 - (1 - beta) * |x j i - rho j|) :=
      Finset.sum_le_sum fun i _ => h.2 j i
    _ = totalWeight w j.val - (1 - beta) *
        (∑ i : Fin n, w j.val i * |x j i - rho j|) := by
      simp only [totalWeight, mul_sub, mul_one, Finset.sum_sub_distrib,
        Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intros
      ring
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left habs hb]

lemma decreasing (h : PotentialConditions beta w x rho) (j : Fin t) :
    totalWeight w (j.val + 1) ≤ totalWeight w j.val := by
  apply Finset.sum_le_sum
  intro i hi
  have hn := h.1.2.2.2.2.1 j.val (Nat.le_of_lt j.isLt) i
  have hb : 0 ≤ 1 - beta := by linarith [h.1.2.2.1]
  have hu := h.2 j i
  nlinarith [abs_nonneg (x j i - rho j), mul_nonneg hb (abs_nonneg (x j i - rho j))]

lemma mono (h : PotentialConditions beta w x rho) {a b : ℕ} (hab : a ≤ b)
    (hbt : b ≤ t) : totalWeight w b ≤ totalWeight w a := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih =>
    exact (decreasing h ⟨b, by omega⟩).trans (ih (by omega))

lemma positive (h : PotentialConditions beta w x rho)
    (hfin : 0 < totalWeight w t) {k : ℕ} (hk : k ≤ t) :
    0 < totalWeight w k := lt_of_lt_of_le hfin (mono h hk le_rfl)

lemma log_bound (h : PotentialConditions beta w x rho)
    (hfin : 0 < totalWeight w t) :
    Real.log (totalWeight w t / totalWeight w 0) ≤
      ∑ j : Fin t, Real.log (1 - (1 - beta) * |meanPrediction w x j - rho j|) := by
  have hp : ∀ {k : ℕ}, k ≤ t → 0 < totalWeight w k := fun hk => positive h hfin hk
  have hs : ∀ j : Fin t, Real.log (totalWeight w (j.val + 1)) -
      Real.log (totalWeight w j.val) ≤
      Real.log (1 - (1 - beta) * |meanPrediction w x j - rho j|) := by
    intro j
    have hj := hp (Nat.le_of_lt j.isLt)
    have hj' := hp (show j.val + 1 ≤ t by omega)
    have hstep := step h j hj
    have hf : 0 < 1 - (1 - beta) * |meanPrediction w x j - rho j| := by
      nlinarith
    have hl := Real.log_le_log hj' hstep
    rw [Real.log_mul (ne_of_gt hj) (ne_of_gt hf)] at hl
    linarith
  have htelescope : (∑ j : Fin t, (Real.log (totalWeight w (j.val + 1)) -
      Real.log (totalWeight w j.val))) = Real.log (totalWeight w t) -
      Real.log (totalWeight w 0) := by
    rw [← Finset.sum_range (fun k => Real.log (totalWeight w (k + 1)) -
      Real.log (totalWeight w k))]
    exact Finset.sum_range_sub (fun k => Real.log (totalWeight w k)) t
  rw [Real.log_div (ne_of_gt hfin) (ne_of_gt (hp (Nat.zero_le t))),
    ← htelescope]
  exact Finset.sum_le_sum fun j _ => hs j

lemma loss_bound (h : PotentialConditions beta w x rho)
    (hfin : 0 < totalWeight w t) :
    masterLoss w x rho ≤ Real.log (totalWeight w 0 / totalWeight w t) / (1 - beta) := by
  have hb : 0 < 1 - beta := by linarith [h.1.2.2.1]
  have hp : ∀ {k : ℕ}, k ≤ t → 0 < totalWeight w k := fun hk => positive h hfin hk
  have hf : ∀ j : Fin t, 0 < 1 - (1 - beta) * |meanPrediction w x j - rho j| := by
    intro j
    have hj := hp (Nat.le_of_lt j.isLt)
    have hj' := hp (show j.val + 1 ≤ t by omega)
    have hu := step h j hj
    nlinarith
  have hl := log_bound h hfin
  have hs : (∑ j : Fin t, Real.log (1 - (1 - beta) * |meanPrediction w x j - rho j|)) ≤
      -(1 - beta) * masterLoss w x rho := by
    unfold masterLoss
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hr := Real.log_le_sub_one_of_pos (hf j)
    linarith
  rw [le_div_iff₀ hb]
  rw [Real.log_div (ne_of_gt (hp (Nat.zero_le t))) (ne_of_gt hfin)]
  rw [Real.log_div (ne_of_gt hfin) (ne_of_gt (hp (Nat.zero_le t)))] at hl
  nlinarith

lemma exhausted (h : PotentialConditions beta w x rho) (hb : beta = 0)
    (hl : ∃ j : Fin t, |meanPrediction w x j - rho j| = 1) : totalWeight w t = 0 := by
  have hn := weight_nonneg h (k := t) le_rfl
  by_contra hne
  have hpfin : 0 < totalWeight w t := lt_of_le_of_ne hn (Ne.symm hne)
  obtain ⟨j, hj⟩ := hl
  have hp := positive h hpfin (Nat.le_of_lt j.isLt)
  have hp' := positive h hpfin (show j.val + 1 ≤ t by omega)
  have hs := step h j hp
  rw [hb, hj] at hs
  norm_num at hs
  linarith

lemma run_conditions (h : IsWMCRun beta w x rho) : PotentialConditions beta w x rho := by
  refine ⟨h.1, ?_⟩
  intro j i
  obtain ⟨F, hF, hF', hw⟩ := h.2 j i
  rw [hw, mul_comm]
  exact mul_le_mul_of_nonneg_left hF' (h.1.2.2.2.2.1 j.val (Nat.le_of_lt j.isLt) i)

end ContinuousProof

theorem solution {n t : ℕ} (beta : ℝ) (w : ℕ → Fin n → ℝ)
    (x : Fin t → Fin n → ℝ) (rho : Fin t → ℝ)
    (h : IsWMCRun beta w x rho) (hfin : 0 < WeightedMajority.Basic.totalWeight w t) :
    masterLoss w x rho ≤
      Real.log (WeightedMajority.Basic.totalWeight w 0 / WeightedMajority.Basic.totalWeight w t) / (1 - beta) := by
  exact ContinuousProof.loss_bound (ContinuousProof.run_conditions h) hfin

#print axioms solution
