-- Prove2me | solution 1 for OfflinePolicyLearning.Regret.eq17_dr_error_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T23:28:45.223774+00:00
-- url     : https://prove2.me/submissions/25739865-cf84-4534-b8f9-b49603faae46

import Mathlib
import Definitions.Def_OfflinePolicyLearning_Regret_Hamming
import Definitions.Def_OfflinePolicyLearning_Regret_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open OfflinePolicyLearning.Regret

theorem solution {X : Type*} [MeasurableSpace X] {d K n : ℕ}
    (M : Model X d) (C : CrossFit X d K) (D : Fin n → Draw X d) (πa πb : X → Fin d) :
    C.Δhat D πa πb - M.Δtilde D πa πb =
      ∑ j : Fin d,
        ((1 / n : ℝ) * ∑ i : Fin n,
            ((if πa (D i).1 = j then 1 else 0) - (if πb (D i).1 = j then 1 else 0)) *
              (C.μhatAt D i j - M.μ (D i).1 j) *
              (1 - (if (obs (D i)).2.1 = j then 1 else 0) / M.e (D i).1 j)
          + (1 / n : ℝ) * ∑ i ∈ Finset.univ.filter (fun i : Fin n => (obs (D i)).2.1 = j),
            ((if πa (D i).1 = j then 1 else 0) - (if πb (D i).1 = j then 1 else 0)) *
              ((obs (D i)).2.2 - M.μ (D i).1 j) *
              (1 / C.ehatAt D i j - 1 / M.e (D i).1 j)
          + (1 / n : ℝ) * ∑ i ∈ Finset.univ.filter (fun i : Fin n => (obs (D i)).2.1 = j),
            ((if πa (D i).1 = j then 1 else 0) - (if πb (D i).1 = j then 1 else 0)) *
              (M.μ (D i).1 j - C.μhatAt D i j) *
              (1 / C.ehatAt D i j - 1 / M.e (D i).1 j)) := by
  -- coordinate-wise decomposition of the score error
  have key : ∀ i : Fin n, ∀ j : Fin d, C.GammaHat D i j - M.Γ (obs (D i)) j =
      (C.μhatAt D i j - M.μ (D i).1 j) * (1 - (if (obs (D i)).2.1 = j then 1 else 0) / M.e (D i).1 j)
      + (if (obs (D i)).2.1 = j then
          ((obs (D i)).2.2 - M.μ (D i).1 j) * (1 / C.ehatAt D i j - 1 / M.e (D i).1 j)
          + (M.μ (D i).1 j - C.μhatAt D i j) * (1 / C.ehatAt D i j - 1 / M.e (D i).1 j)
        else 0) := by
    intro i j
    unfold CrossFit.GammaHat Model.Γ
    simp only [obs]
    by_cases h : (D i).2.2 = j
    · subst h; simp only [if_true]; ring
    · simp only [h, if_false]; ring
  -- evaluating a function at an action as an inner product with the one-hot vector
  have onehot : ∀ (f : Fin d → ℝ) (p q : Fin d), f p - f q =
      ∑ j, ((if p = j then 1 else 0) - (if q = j then 1 else 0)) * f j := by
    intro f p q
    simp [sub_mul, Finset.sum_sub_distrib, ite_mul]
  have lhs : C.Δhat D πa πb - M.Δtilde D πa πb = (1 / n : ℝ) * ∑ i : Fin n, ∑ j : Fin d,
      ((if πa (D i).1 = j then 1 else 0) - (if πb (D i).1 = j then 1 else 0)) *
        (C.GammaHat D i j - M.Γ (obs (D i)) j) := by
    have : ∀ i : Fin n, ∑ j : Fin d,
      ((if πa (D i).1 = j then (1:ℝ) else 0) - (if πb (D i).1 = j then 1 else 0)) *
        (C.GammaHat D i j - M.Γ (obs (D i)) j) =
        (C.GammaHat D i (πa (D i).1) - C.GammaHat D i (πb (D i).1)) -
          (M.Γ (obs (D i)) (πa (D i).1) - M.Γ (obs (D i)) (πb (D i).1)) := by
      intro i
      rw [onehot (fun j => C.GammaHat D i j), onehot (fun j => M.Γ (obs (D i)) j),
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    simp only [this]
    unfold CrossFit.Δhat CrossFit.Qhat Model.Δtilde Model.Qtilde
    simp only [Finset.sum_sub_distrib]
    ring
  rw [lhs]
  simp only [Finset.sum_filter, ← mul_add, ← Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [key]
  split_ifs <;> ring
