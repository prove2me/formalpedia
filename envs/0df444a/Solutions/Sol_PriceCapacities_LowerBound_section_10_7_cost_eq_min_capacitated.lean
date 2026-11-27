-- Prove2me | solution 1 for PriceCapacities.LowerBound.section_10_7_cost_eq_min_capacitated
-- status  : ACCEPTED   (prove)
-- author  : @DavidDenisov
-- created : 2026-11-26T23:53:12.88479+00:00
-- url     : https://prove2.me/submissions/22aafdf0-85a6-425e-83a9-2b86035f2b04

import Mathlib
import Definitions.Def_PriceCapacities_LowerBound_WeightedSets
import Definitions.Def_PriceCapacities_LowerBound_CapacitatedCost
import Definitions.Def_PriceCapacities_LowerBound_CapacitatedCoreset
import Definitions.Def_PriceCapacities_LowerBound_DualCost

set_option autoImplicit false

open PriceCapacities
open PriceCapacities.LowerBound

theorem solution (d k z : ℕ) (hk : 1 ≤ k) (hz : 1 ≤ z) :
    (∀ (S : WeightedSet (EuclideanSpace ℝ (Fin d))) (C : Fin k → EuclideanSpace ℝ (Fin d)),
      (∃ h : Fin k → ℝ, IsFeasibleLoad (totalWeight S) h ∧
          unconstrainedCost (z : ℝ) S C = capCost (z : ℝ) S C h) ∧
        ∀ h : Fin k → ℝ, IsFeasibleLoad (totalWeight S) h →
          unconstrainedCost (z : ℝ) S C ≤ capCost (z : ℝ) S C h) ∧
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ P Q : WeightedSet (EuclideanSpace ℝ (Fin d)), IsCapacitatedCoreset k (z : ℝ) ε P Q →
        ∀ C : Fin k → EuclideanSpace ℝ (Fin d),
          |unconstrainedCost (z : ℝ) Q C - unconstrainedCost (z : ℝ) P C|
            ≤ ε * unconstrainedCost (z : ℝ) P C := by
  classical
  let X := EuclideanSpace ℝ (Fin d)
  let _ : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  have minimum (S : WeightedSet X) (C : Fin k → X) :
      (∃ h : Fin k → ℝ, IsFeasibleLoad (totalWeight S) h ∧
        unconstrainedCost (z : ℝ) S C = capCost (z : ℝ) S C h) ∧
      ∀ h : Fin k → ℝ, IsFeasibleLoad (totalWeight S) h →
        unconstrainedCost (z : ℝ) S C ≤ capCost (z : ℝ) S C h := by
    let value (x : X) (i : Fin k) := dist x (C i) ^ (z : ℝ)
    have chooser (x : X) : ∃ i, ∀ j, value x i ≤ value x j := by
      obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ (value x) Finset.univ_nonempty
      exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩
    choose winner hwin using chooser
    have price (x : X) : pricedCost (z : ℝ) C (fun _ => 0) x = value x (winner x) := by
      unfold pricedCost
      simp only [add_zero]
      exact le_antisymm (ciInf_le (Set.finite_range _).bddBelow _) (le_ciInf (hwin x))
    have lower (h : Fin k → ℝ) (a : X → Fin k → ℝ) (ha : IsLoadAssignment S h a) :
        unconstrainedCost (z : ℝ) S C ≤ assignmentCost (z : ℝ) S C a := by
      unfold unconstrainedCost wsum assignmentCost
      refine Finset.sum_le_sum fun x hx => ?_
      rw [price, ← ha.2.1 x hx, Finset.sum_mul]
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hwin x i) (ha.1 x i)
    have total : totalWeight S = ∑ x ∈ S.support, (S x : ℝ) := by simp [totalWeight, wsum]
    have feasible (h : Fin k → ℝ) (hh : IsFeasibleLoad (totalWeight S) h) :
        ∃ a : X → Fin k → ℝ, IsLoadAssignment S h a := by
      let a (x : X) (i : Fin k) := (S x : ℝ) * (h i / totalWeight S)
      have nonneg : 0 ≤ totalWeight S := by
        rw [total]
        exact Finset.sum_nonneg fun _ _ => NNReal.zero_le_coe
      refine ⟨a, fun x i => mul_nonneg NNReal.zero_le_coe (div_nonneg (hh.1 i) nonneg), ?_, ?_⟩
      · intro x hx
        dsimp [a]
        rw [← Finset.mul_sum, ← Finset.sum_div, hh.2, div_self, mul_one]
        intro hzero
        have hw := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => NNReal.zero_le_coe (q := S y))).1
          (total.symm.trans hzero) x hx
        exact (Finsupp.mem_support_iff.mp hx) (by exact_mod_cast hw)
      · intro i
        dsimp [a]
        rw [← Finset.sum_mul, ← total]
        by_cases hzero : totalWeight S = 0
        · have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hh.1 j)).1
            (hh.2.trans hzero) i (Finset.mem_univ i)
          rw [hzero, zero_mul, hi]
        · field_simp
    have cap_lower (h : Fin k → ℝ) (hh : IsFeasibleLoad (totalWeight S) h) :
        unconstrainedCost (z : ℝ) S C ≤ capCost (z : ℝ) S C h := by
      obtain ⟨a, ha⟩ := feasible h hh
      unfold capCost
      refine le_csInf ⟨_, a, ha, rfl⟩ ?_
      rintro _ ⟨b, hb, rfl⟩
      exact lower h b hb
    let a (x : X) (i : Fin k) : ℝ := if i = winner x then S x else 0
    let h (i : Fin k) := ∑ x ∈ S.support, a x i
    have nonneg_a (x : X) (i : Fin k) : 0 ≤ a x i := by dsimp [a]; split <;> positivity
    have rows (x : X) : ∑ i, a x i = (S x : ℝ) := by simp [a]
    have hh : IsFeasibleLoad (totalWeight S) h := by
      refine ⟨fun i => Finset.sum_nonneg fun x _ => nonneg_a x i, ?_⟩
      dsimp [h]
      rw [Finset.sum_comm, total]
      exact Finset.sum_congr rfl fun x _ => rows x
    have hassign : IsLoadAssignment S h a := ⟨nonneg_a, fun x _ => rows x, fun _ => rfl⟩
    have hvalue : assignmentCost (z : ℝ) S C a = unconstrainedCost (z : ℝ) S C := by
      unfold assignmentCost unconstrainedCost wsum
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [price]
      simp [a, value]
    refine ⟨⟨h, hh, le_antisymm (cap_lower h hh) ?_⟩, cap_lower⟩
    unfold capCost
    rw [← hvalue]
    exact csInf_le ⟨unconstrainedCost (z : ℝ) S C, by
      rintro _ ⟨b, hb, rfl⟩; exact lower h b hb⟩ ⟨a, hassign, rfl⟩
  refine ⟨minimum, ?_⟩
  intro ε _ hε P Q hQ C
  obtain ⟨⟨hP, hhP, optP⟩, boundP⟩ := minimum P C
  obtain ⟨⟨hQ', hhQ', optQ⟩, boundQ⟩ := minimum Q C
  have same := hQ.1
  have upper := (abs_le.mp (hQ.2 C hP hhP)).2
  have lower := (abs_le.mp (hQ.2 C hQ' (same ▸ hhQ'))).1
  have Qle := boundQ hP (same.symm ▸ hhP)
  have Ple := boundP hQ' (same ▸ hhQ')
  apply abs_le.mpr
  constructor
  · rw [optQ] at ⊢
    have hmul := mul_le_mul_of_nonneg_left Ple (sub_nonneg.mpr hε.le)
    linarith
  · rw [optP]
    linarith
