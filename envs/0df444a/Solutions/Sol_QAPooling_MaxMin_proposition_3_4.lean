-- Prove2me | solution 1 for QAPooling.MaxMin.proposition_3_4
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T09:31:54.50778+00:00
-- url     : https://prove2.me/submissions/1b448e51-2a85-4186-a865-cd2465c489e0

import Mathlib
import Definitions.Def_QAPooling_MaxMin_Model

-- Complete inline checked helper module: FiniteScore.lean

namespace QAPooling.MaxMin.SavageProof

lemma coe_sum {ι : Type*} (t : Finset ι) (f : ι → ℝ) :
    ((∑ j ∈ t, f j : ℝ) : EReal) = ∑ j ∈ t, (f j : EReal) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih => simp [Finset.sum_insert hi, EReal.coe_add, ih]

lemma expectedScore_eq_coe_sum {n : ℕ} (s : ScoringRule n) (p q : Fin n → ℝ)
    (htop : ∀ j, s q j ≠ ⊤) (hzero : ∀ j, s q j = ⊥ → p j = 0) :
    expectedScore s p q = ((∑ j, p j * (s q j).toReal : ℝ) : EReal) := by
  rw [coe_sum]
  unfold expectedScore
  apply Finset.sum_congr rfl
  intro j _
  by_cases hb : s q j = ⊥
  · simp [hzero j hb]
  · rw [EReal.coe_mul, EReal.coe_toReal (htop j) hb]

lemma regular_self_score {n : ℕ} (s : ScoringRule n) (hreg : IsRegular s)
    (p : Fin n → ℝ) (hp : p ∈ stdSimplex ℝ (Fin n)) :
    expectedScore s p p = (expectedReward s p : EReal) := by
  have he := expectedScore_eq_coe_sum s p p (fun j => (hreg p hp j).1)
    (fun j => (hreg p hp j).2)
  unfold expectedReward
  rw [he, EReal.toReal_coe]

lemma reward_eq_sum {n : ℕ} (s : ScoringRule n) (hreg : IsRegular s)
    (p : Fin n → ℝ) (hp : p ∈ stdSimplex ℝ (Fin n)) :
    expectedReward s p = ∑ j, p j * (s p j).toReal := by
  unfold expectedReward
  rw [expectedScore_eq_coe_sum s p p (fun j => (hreg p hp j).1)
    (fun j => (hreg p hp j).2), EReal.toReal_coe]

lemma score_le_reward {n : ℕ} (s : ScoringRule n) (hreg : IsRegular s) (hprop : IsProper s)
    (p q : Fin n → ℝ) (hp : p ∈ stdSimplex ℝ (Fin n)) (hq : q ∈ stdSimplex ℝ (Fin n))
    (hzero : ∀ j, s q j = ⊥ → p j = 0) :
    (∑ j, p j * (s q j).toReal) ≤ expectedReward s p := by
  have hh := (hprop p hp q hq).1
  rw [expectedScore_eq_coe_sum s p q (fun j => (hreg q hq j).1) hzero,
    regular_self_score s hreg p hp] at hh
  exact EReal.coe_le_coe_iff.mp hh

end QAPooling.MaxMin.SavageProof


-- Complete inline checked helper module: Exposure.lean

namespace QAPooling.MaxMin.BregmanProof

lemma sum_real_coe {ι : Type*} (t : Finset ι) (a : ι → ℝ) :
    (∑ j ∈ t, (a j : EReal)) = ((∑ j ∈ t, a j : ℝ) : EReal) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert j t hj ih => simp [hj,ih, EReal.coe_add]

lemma exposure_outcome {n : ℕ} (g q : Fin n → ℝ) (G : ℝ) (j : Fin n) :
    G + ∑ k, g k * ((Pi.single j (1 : ℝ) : Fin n → ℝ) k-q k) =
      G + g j - ∑ k, g k*q k := by
  classical
  simp only [mul_sub, Finset.sum_sub_distrib]
  simp [Pi.single_apply, mul_ite, add_sub_assoc]

lemma exposure_average {n : ℕ} (g q x : Fin n → ℝ) (hx : x ∈ stdSimplex ℝ (Fin n)) (G : ℝ) :
    (∑ j, x j*(G+∑ k,g k*((Pi.single j (1 : ℝ) : Fin n → ℝ) k-q k))) =
      G+∑ k,g k*(x k-q k) := by
  simp_rw [exposure_outcome, mul_sub, mul_add]
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.sum_mul,← Finset.sum_mul,hx.2]
  simp only [one_mul]
  rw [Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl (fun j _ => mul_comm (x j) (g j))]
  ring

lemma exposure_expectation {n : ℕ} (s : ScoringRule n) (g : (Fin n → ℝ) → Fin n → ℝ)
    (hg : IsExposure s g) (q : Fin n → ℝ) (hq : q ∈ forecastDomain s)
    (x : Fin n → ℝ) (hx : x ∈ stdSimplex ℝ (Fin n)) :
    expectedScore s x q = ((expectedReward s q + ∑ k,g q k*(x k-q k) : ℝ) : EReal) := by
  unfold expectedScore
  simp_rw [hg q hq, ← EReal.coe_mul]
  rw [sum_real_coe, exposure_average (g q) q x hx]

end QAPooling.MaxMin.BregmanProof

-- Complete inline checked helper module: Main.lean

open QAPooling.MaxMin QAPooling.MaxMin.BregmanProof

local notation "IsRegular" => QAPooling.MaxMin.IsRegular

theorem solution {n : ℕ} (s : ScoringRule n) (g : (Fin n → ℝ) → Fin n → ℝ)
    (hreg : IsRegular s) (hprop : IsProper s) (hg : IsExposure s g)
    (q : Fin n → ℝ) (hq : q ∈ forecastDomain s) (x : Fin n → ℝ) (hx : x ∈ stdSimplex ℝ (Fin n)) :
    0 ≤ bregman s g x q ∧ (bregman s g x q = 0 → x = q) := by
  have hh := hprop x hx q hq.1
  rw [exposure_expectation s g hg q hq x hx, SavageProof.regular_self_score s hreg x hx] at hh
  have hle := EReal.coe_le_coe_iff.mp hh.1
  constructor
  · unfold bregman
    linarith
  · intro hz
    have he : expectedReward s q + ∑ k, g q k*(x k-q k) = expectedReward s x := by
      unfold bregman at hz
      linarith
    exact (hh.2 (congrArg (fun r : ℝ => (r : EReal)) he)).symm
