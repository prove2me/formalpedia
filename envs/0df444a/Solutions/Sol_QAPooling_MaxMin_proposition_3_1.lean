-- Prove2me | solution 1 for QAPooling.MaxMin.proposition_3_1
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T09:33:00.711862+00:00
-- url     : https://prove2.me/submissions/4415966f-ce5c-4c88-b935-61863085918a

import Mathlib
import Definitions.Def_QAPooling_MaxMin_Model

-- Complete inline local helper: FiniteScore.lean

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


-- Complete inline local helper: Exposure.lean

namespace QAPooling.MaxMin.SavageProof

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

end QAPooling.MaxMin.SavageProof

-- Complete inline local helper: Convexity.lean

namespace QAPooling.MaxMin.SavageProof

lemma reward_convex {n : ℕ} (s : ScoringRule n) (hreg : IsRegular s) (hprop : IsProper s) :
    ConvexOn ℝ (stdSimplex ℝ (Fin n)) (expectedReward s) := by
  refine ⟨convex_stdSimplex ℝ (Fin n), ?_⟩
  intro x hx y hy a b ha hb hab
  by_cases ha0 : a=0
  · have hb1 : b=1 := by linarith
    simp [ha0,hb1]
  by_cases hb0 : b=0
  · have ha1 : a=1 := by linarith
    simp [hb0,ha1]
  let q := a • x+b • y
  have hq : q ∈ stdSimplex ℝ (Fin n) := convex_stdSimplex ℝ (Fin n) hx hy ha hb hab
  have hzero (j : Fin n) (hbot : s q j=⊥) : x j=0 ∧ y j=0 := by
    have hz := (hreg q hq j).2 hbot
    change a*x j+b*y j=0 at hz
    have hax : 0 ≤ a*x j := mul_nonneg ha (hx.1 j)
    have hby : 0 ≤ b*y j := mul_nonneg hb (hy.1 j)
    have hex : a*x j=0 := by linarith
    have hey : b*y j=0 := by linarith
    exact ⟨(mul_eq_zero.mp hex).resolve_left ha0,(mul_eq_zero.mp hey).resolve_left hb0⟩
  have hxb := score_le_reward s hreg hprop x q hx hq (fun j hj => (hzero j hj).1)
  have hyb := score_le_reward s hreg hprop y q hy hq (fun j hj => (hzero j hj).2)
  have heq : expectedReward s q =
      a*(∑ j,x j*(s q j).toReal)+b*(∑ j,y j*(s q j).toReal) := by
    rw [reward_eq_sum s hreg q hq]
    change (∑ j,(a*x j+b*y j)*(s q j).toReal)=_
    simp_rw [add_mul,mul_assoc]
    rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
  change expectedReward s q ≤ a*expectedReward s x+b*expectedReward s y
  rw [heq]
  exact add_le_add (mul_le_mul_of_nonneg_left hxb ha) (mul_le_mul_of_nonneg_left hyb hb)

end QAPooling.MaxMin.SavageProof


namespace QAPooling.MaxMin.SavageProof

lemma score_exposure {n : ℕ} (s : ScoringRule n) (hreg : IsRegular s) :
    IsExposure s (fun p j => (s p j).toReal) := by
  intro p hp j
  have hsum : (∑ k,(s p k).toReal*p k)=expectedReward s p := by
    rw [reward_eq_sum s hreg p hp.1]
    exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
  calc
    s p j = ((s p j).toReal : EReal) := (EReal.coe_toReal (hp.2 j).2 (hp.2 j).1).symm
    _ = _ := by
      congr 1
      rw [exposure_outcome,hsum]
      ring

lemma exposure_subgradient {n : ℕ} (s : ScoringRule n) (hreg : IsRegular s) (hprop : IsProper s)
    (g : (Fin n → ℝ) → Fin n → ℝ) (hg : IsExposure s g)
    (q : Fin n → ℝ) (hq : q ∈ forecastDomain s) :
    IsSubgradientOn (expectedReward s) (g q) q := by
  intro y hy
  have hh := (hprop y hy q hq.1).1
  rw [exposure_expectation s g hg q hq y hy,regular_self_score s hreg y hy] at hh
  exact EReal.coe_le_coe_iff.mp hh

end QAPooling.MaxMin.SavageProof

namespace QAPooling.MaxMin

theorem _root_.solution {n : ℕ} (s : ScoringRule n) (hreg : IsRegular s) (hprop : IsProper s) :
    ConvexOn ℝ (stdSimplex ℝ (Fin n)) (expectedReward s) ∧
      IsExposure s (fun p j => (s p j).toReal) ∧
      ∀ g : (Fin n → ℝ) → Fin n → ℝ, IsExposure s g →
        ∀ q ∈ forecastDomain s, IsSubgradientOn (expectedReward s) (g q) q := by
  exact ⟨SavageProof.reward_convex s hreg hprop,SavageProof.score_exposure s hreg,
    SavageProof.exposure_subgradient s hreg hprop⟩

end QAPooling.MaxMin
