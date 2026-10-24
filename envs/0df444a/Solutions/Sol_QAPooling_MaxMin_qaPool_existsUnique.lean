-- Prove2me | solution 1 for QAPooling.MaxMin.qaPool_existsUnique
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T09:40:06.573111+00:00
-- url     : https://prove2.me/submissions/7460aa11-c91f-4484-b057-df594c7a0b1d

import Mathlib
import Definitions.Def_QAPooling_MaxMin_Model

-- Complete finite-score helpers adapted from the checked sibling Savage proof.
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

-- Strict convexity on the entire simplex, including its boundary.
namespace QAPooling.MaxMin.ExistenceProof

open SavageProof

lemma reward_strictConvex {n : ℕ} (s : ScoringRule n) (hreg : IsRegular s)
    (hprop : IsProper s) :
    StrictConvexOn ℝ (stdSimplex ℝ (Fin n)) (expectedReward s) := by
  refine ⟨convex_stdSimplex ℝ (Fin n), ?_⟩
  intro x hx y hy hxy a b ha hb hab
  let q := a • x+b • y
  have hq : q ∈ stdSimplex ℝ (Fin n) := convex_stdSimplex ℝ (Fin n) hx hy ha.le hb.le hab
  have hzero (j : Fin n) (hbot : s q j=⊥) : x j=0 ∧ y j=0 := by
    have hz := (hreg q hq j).2 hbot
    change a*x j+b*y j=0 at hz
    have hax : 0 ≤ a*x j := mul_nonneg ha.le (hx.1 j)
    have hby : 0 ≤ b*y j := mul_nonneg hb.le (hy.1 j)
    have hex : a*x j=0 := by linarith
    have hey : b*y j=0 := by linarith
    exact ⟨(mul_eq_zero.mp hex).resolve_left ha.ne',(mul_eq_zero.mp hey).resolve_left hb.ne'⟩
  have hqx : q ≠ x := by
    intro he
    apply hxy
    funext j
    have hj := congrFun he j
    change a*x j+b*y j=x j at hj
    have hz : b*(x j-y j)=0 := by nlinarith [congrArg (fun t : ℝ => t*x j) hab]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hb.ne')
  have hxb : (∑ j, x j*(s q j).toReal) < expectedReward s x := by
    have hh := (hprop x hx q hq).1
    have hne : expectedScore s x q ≠ expectedScore s x x := fun h => hqx ((hprop x hx q hq).2 h)
    have hlt := lt_of_le_of_ne hh hne
    rw [expectedScore_eq_coe_sum s x q (fun j => (hreg q hq j).1)
      (fun j hj => (hzero j hj).1), regular_self_score s hreg x hx] at hlt
    exact EReal.coe_lt_coe_iff.mp hlt
  have hyb := score_le_reward s hreg hprop y q hy hq (fun j hj => (hzero j hj).2)
  have heq : expectedReward s q =
      a*(∑ j,x j*(s q j).toReal)+b*(∑ j,y j*(s q j).toReal) := by
    rw [reward_eq_sum s hreg q hq]
    change (∑ j,(a*x j+b*y j)*(s q j).toReal)=_
    simp_rw [add_mul,mul_assoc]
    rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
  change expectedReward s q < a*expectedReward s x+b*expectedReward s y
  rw [heq]
  exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hxb ha)
    (mul_le_mul_of_nonneg_left hyb hb.le)

lemma subgradient_iff_isMinOn {n : ℕ} (G : (Fin n → ℝ) → ℝ) (v x : Fin n → ℝ) :
    IsSubgradientOn G v x ↔
      IsMinOn (fun y => G y - ∑ j, v j*y j) (stdSimplex ℝ (Fin n)) x := by
  change (∀ y ∈ stdSimplex ℝ (Fin n), G x + ∑ j, v j*(y j-x j) ≤ G y) ↔
    ∀ y ∈ stdSimplex ℝ (Fin n), G x - ∑ j, v j*x j ≤ G y - ∑ j, v j*y j
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  constructor <;> intro h y hy <;> have hh := h y hy <;> linarith

end QAPooling.MaxMin.ExistenceProof

namespace QAPooling.MaxMin

open ExistenceProof

/-- The QA pool is well-defined (§3.2, p. 12): for forecasts in `D` with non-negative weights adding
to 1, there is exactly one `p* ∈ Δⁿ` at which `Σ_i w_i g(p_i)` is a subgradient of `G`. -/
theorem _root_.solution {n m : ℕ} (s : ScoringRule n) (g : (Fin n → ℝ) → Fin n → ℝ)
    (hreg : IsRegular s) (hprop : IsProper s)
    (hGcont : ContinuousOn (expectedReward s) (stdSimplex ℝ (Fin n)))
    (hg : IsExposure s g)
    (p : Fin m → Fin n → ℝ) (hp : ∀ i, p i ∈ forecastDomain s)
    (w : Fin m → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) :
    ∃! pstar, IsQAPool s g p w pstar := by
  have hm : 0 < m := by
    by_contra h
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos h
    subst m
    simp at hw1
  have hne : (stdSimplex ℝ (Fin n)).Nonempty := ⟨p ⟨0, hm⟩, (hp ⟨0, hm⟩).1⟩
  let v : Fin n → ℝ := fun j => ∑ i, w i * g (p i) j
  let f : (Fin n → ℝ) →ₗ[ℝ] ℝ := dotProductBilin ℝ ℝ v
  let F : (Fin n → ℝ) → ℝ := fun x => expectedReward s x - f x
  have hcont : ContinuousOn F (stdSimplex ℝ (Fin n)) :=
    hGcont.sub f.continuous_of_finiteDimensional.continuousOn
  have hstrict : StrictConvexOn ℝ (stdSimplex ℝ (Fin n)) F :=
    (reward_strictConvex s hreg hprop).sub_concaveOn (f.concaveOn (convex_stdSimplex ℝ (Fin n)))
  obtain ⟨x, hx, hmin⟩ := (isCompact_stdSimplex ℝ (Fin n)).exists_isMinOn hne hcont
  have hxsub : IsSubgradientOn (expectedReward s) v x :=
    (subgradient_iff_isMinOn (expectedReward s) v x).mpr hmin
  refine ⟨x, ⟨hx, hxsub⟩, ?_⟩
  intro y hy
  have hymin : IsMinOn F (stdSimplex ℝ (Fin n)) y :=
    (subgradient_iff_isMinOn (expectedReward s) v y).mp hy.2
  exact (hstrict.eq_of_isMinOn hmin hymin hx hy.1).symm

end QAPooling.MaxMin
