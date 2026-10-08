-- Prove2me | solution 1 for SuttonBartoRL.PolicyGradient.bellman_episodic
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:36:48.436354+00:00
-- url     : https://prove2.me/submissions/86251fcc-5a31-403c-9526-97bbbbdb2a74

import Mathlib
import Definitions.Def_SuttonBartoRL_PolicyGradient_Model
import Definitions.Def_SuttonBartoRL_PolicyGradient_EpisodicValues

set_option autoImplicit false

namespace SuttonBartoRL.PolicyGradient.EpisodicMDP

lemma bell199_u_summable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] {d : ℕ}
    (M : EpisodicMDP S A) (π : ParamPolicy S A d) (θ : EuclideanSpace ℝ (Fin d))
    (hT : M.Terminates π θ) (s : S) :
    Summable (fun k : ℕ => Matrix.mulVec (policyTrans M π θ ^ k) (policyReward M π θ) s) := by
  simp only [Matrix.mulVec, dotProduct]
  exact summable_sum (fun j _ => (hT s j).mul_right _)

lemma bell199_u_succ {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] {d : ℕ}
    (M : EpisodicMDP S A) (π : ParamPolicy S A d) (θ : EuclideanSpace ℝ (Fin d))
    (k : ℕ) (s : S) :
    Matrix.mulVec (policyTrans M π θ ^ (k + 1)) (policyReward M π θ) s =
      ∑ s', policyTrans M π θ s s' * Matrix.mulVec (policyTrans M π θ ^ k) (policyReward M π θ) s' := by
  rw [pow_succ', ← Matrix.mulVec_mulVec]
  rfl

lemma bell199_inner_summable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] {d : ℕ}
    (M : EpisodicMDP S A) (π : ParamPolicy S A d) (θ : EuclideanSpace ℝ (Fin d))
    (hT : M.Terminates π θ) (s : S) (a : A) :
    Summable (fun k : ℕ => ∑ s', M.trans s a s' *
      Matrix.mulVec (policyTrans M π θ ^ k) (policyReward M π θ) s') :=
  summable_sum (fun j _ => (bell199_u_summable M π θ hT j).mul_left _)

end SuttonBartoRL.PolicyGradient.EpisodicMDP

open SuttonBartoRL.PolicyGradient in
theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] {d : ℕ}
    (M : EpisodicMDP S A) (π : ParamPolicy S A d) (θ : EuclideanSpace ℝ (Fin d))
    (hT : M.Terminates π θ) :
    (∀ s, M.stateValue π θ s = ∑ a, π.prob θ s a * M.actionValue π θ s a) ∧
    (∀ s a, M.actionValue π θ s a =
      ∑ s' : Option S, ∑ r ∈ M.R,
        M.p s a s' r * (r + EpisodicMDP.valuePlus (M.stateValue π θ) s')) := by
  open SuttonBartoRL.PolicyGradient.EpisodicMDP in
  constructor
  · intro s
    have key : ∀ k : ℕ, ∑ a, π.prob θ s a * ∑ s', M.trans s a s' *
        Matrix.mulVec (policyTrans M π θ ^ k) (policyReward M π θ) s' =
        Matrix.mulVec (policyTrans M π θ ^ (k + 1)) (policyReward M π θ) s := by
      intro k
      rw [bell199_u_succ]
      simp only [policyTrans, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
    have h2 : ∑ a, π.prob θ s a * ∑' k : ℕ, ∑ s', M.trans s a s' *
        Matrix.mulVec (policyTrans M π θ ^ k) (policyReward M π θ) s' =
        ∑' k : ℕ, Matrix.mulVec (policyTrans M π θ ^ (k + 1)) (policyReward M π θ) s := by
      simp_rw [← tsum_mul_left]
      rw [← Summable.tsum_finsetSum (fun a _ => (bell199_inner_summable M π θ hT s a).mul_left _)]
      exact tsum_congr key
    simp only [actionValue, mul_add, Finset.sum_add_distrib]
    rw [h2, stateValue, (bell199_u_summable M π θ hT s).tsum_eq_zero_add]
    congr 1
    simp [policyReward]
  · intro s a
    simp only [mul_add, Finset.sum_add_distrib]
    have e1 : ∑ s' : Option S, ∑ r ∈ M.R, M.p s a s' r * r = M.expReward s a := by
      rw [expReward, Finset.sum_comm]
      refine Finset.sum_congr rfl (fun _ _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun _ _ => by ring)
    have e2 : ∑ s' : Option S, ∑ r ∈ M.R, M.p s a s' r * valuePlus (M.stateValue π θ) s' =
        ∑ s', M.trans s a s' * M.stateValue π θ s' := by
      simp only [← Finset.sum_mul]
      rw [Fintype.sum_option]
      simp [valuePlus, EpisodicMDP.trans]
    rw [e1, e2, actionValue]
    congr 1
    simp only [stateValue]
    simp_rw [← tsum_mul_left]
    rw [Summable.tsum_finsetSum (fun j _ => (bell199_u_summable M π θ hT j).mul_left _)]
