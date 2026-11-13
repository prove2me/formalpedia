-- Prove2me | solution 1 for StabilityDichotomies.Solvability.wasserstein_le_joint_cost
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:01:28.528206+00:00
-- url     : https://prove2.me/submissions/288e132c-5236-4c78-84e9-9eb3e6afc5a2

import Definitions.Def_StabilityDichotomies_Solvability_Stability
noncomputable section
open scoped Classical BigOperators ENNReal
open StabilityDichotomies.Solvability

private theorem first_marginal {A B : Type} [Fintype A] [Fintype B]
    (ρ : PMF (A × B)) (x : A) :
    (∑ y : B, (ρ (x,y)).toReal) = ((ρ.map Prod.fst) x).toReal := by
  rw [PMF.map_apply, tsum_fintype]
  rw [ENNReal.toReal_sum (by intro a ha; split_ifs <;> simp [PMF.apply_ne_top])]
  rw [Fintype.sum_prod_type]
  simp only [apply_ite, ENNReal.toReal_zero]
  have h (a : A) : (∑ y : B, if x = a then (ρ (a,y)).toReal else 0) =
      if x = a then ∑ y : B, (ρ (a,y)).toReal else 0 := by
    by_cases hx : x = a <;> simp [hx]
  simp_rw [h]
  simp

private theorem second_marginal {A B : Type} [Fintype A] [Fintype B]
    (ρ : PMF (A × B)) (y : B) :
    (∑ x : A, (ρ (x,y)).toReal) = ((ρ.map Prod.snd) y).toReal := by
  rw [PMF.map_apply, tsum_fintype]
  rw [ENNReal.toReal_sum (by intro a ha; split_ifs <;> simp [PMF.apply_ne_top])]
  rw [Fintype.sum_prod_type]
  simp only [apply_ite, ENNReal.toReal_zero]
  simp

private theorem wasserstein_le_coupling_cost {V : Type} [Fintype V]
    (μ ν : PMF (V → Bool)) (π : (V → Bool) → (V → Bool) → ℝ)
    (hπ : π ∈ FairProxy.ClosedFormDD.couplingSet
      (fun x => (μ x).toReal) (fun y => (ν y).toReal)) :
    wasserstein μ ν ≤ ∑ x, ∑ y, π x y * hammingCost x y := by
  unfold wasserstein
  apply csInf_le
  · refine ⟨0, ?_⟩
    intro t ht
    obtain ⟨ρ, hρ, rfl⟩ := ht
    apply Finset.sum_nonneg
    intro x hx
    apply Finset.sum_nonneg
    intro y hy
    exact mul_nonneg (hρ.2.2 x y).1 (by simp [hammingCost])
  · exact ⟨π, hπ, rfl⟩

theorem solution {V : Type} [Fintype V]
    (ρ : PMF ((V → Bool) × (V → Bool))) :
    wasserstein (ρ.map Prod.fst) (ρ.map Prod.snd) ≤
      ∑ x, ∑ y, (ρ (x,y)).toReal * hammingCost x y := by
  apply wasserstein_le_coupling_cost (ρ.map Prod.fst) (ρ.map Prod.snd)
    (fun x y => (ρ (x,y)).toReal)
  refine ⟨first_marginal ρ, second_marginal ρ, ?_⟩
  intro x y
  constructor
  · exact ENNReal.toReal_nonneg
  · have h := (ENNReal.toReal_le_toReal (ρ.apply_ne_top (x,y)) ENNReal.one_ne_top).2
      (ρ.coe_le_one (x,y))
    simpa using h

