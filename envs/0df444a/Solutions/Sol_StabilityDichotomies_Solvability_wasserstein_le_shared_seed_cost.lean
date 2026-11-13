-- Prove2me | solution 1 for StabilityDichotomies.Solvability.wasserstein_le_shared_seed_cost
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:08:14.534196+00:00
-- url     : https://prove2.me/submissions/557f75a5-1358-412c-b0ed-b20be18287ef

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

private theorem map_expectation {A Ω : Type} [Fintype A] [Fintype Ω]
    (μ : PMF Ω) (f : Ω → A) (c : A → ℝ) :
    (∑ a : A, ((μ.map f) a).toReal * c a) = ∑ ω : Ω, (μ ω).toReal * c (f ω) := by
  have hh (a : A) : ((μ.map f) a).toReal = ∑ ω : Ω, if a = f ω then (μ ω).toReal else 0 := by
    rw [PMF.map_apply, tsum_fintype]
    rw [ENNReal.toReal_sum (by intro z hz; split_ifs <;> simp [PMF.apply_ne_top])]
    simp only [apply_ite, ENNReal.toReal_zero]
  simp_rw [hh, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω hω
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

private theorem wasserstein_le_joint_cost {V : Type} [Fintype V]
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

theorem solution {V Ω : Type} [Fintype V] [Fintype Ω]
    (μ : PMF Ω) (f g : Ω → V → Bool) :
    wasserstein (μ.map f) (μ.map g) ≤
      ∑ ω, (μ ω).toReal * hammingCost (f ω) (g ω) := by
  let pair : Ω → ((V → Bool) × (V → Bool)) := fun ω => (f ω, g ω)
  have h := wasserstein_le_joint_cost (μ.map pair)
  have heq := map_expectation μ pair (fun p => hammingCost p.1 p.2)
  rw [Fintype.sum_prod_type] at heq
  simp only [PMF.map_comp, pair, Function.comp_def] at h
  rw [heq] at h
  exact h

