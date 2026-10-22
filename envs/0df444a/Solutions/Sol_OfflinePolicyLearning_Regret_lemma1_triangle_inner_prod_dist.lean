-- Prove2me | solution 1 for OfflinePolicyLearning.Regret.lemma1_triangle_inner_prod_dist
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:37:59.760483+00:00
-- url     : https://prove2.me/submissions/e30cf870-fb21-4997-a96d-2eadaedd7b80

import Mathlib
import Definitions.Def_OfflinePolicyLearning_Regret_Hamming
import Definitions.Def_OfflinePolicyLearning_Regret_Setting
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open OfflinePolicyLearning.Regret

lemma jj_mink {ι : Type*} (s : Finset ι) (u v : ι → ℝ) :
    Real.sqrt (∑ i ∈ s, (u i + v i) ^ 2) ≤
      Real.sqrt (∑ i ∈ s, u i ^ 2) + Real.sqrt (∑ i ∈ s, v i ^ 2) := by
  have ha := Real.sqrt_nonneg (∑ i ∈ s, u i ^ 2)
  have hb := Real.sqrt_nonneg (∑ i ∈ s, v i ^ 2)
  have hu : 0 ≤ ∑ i ∈ s, u i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hv : 0 ≤ ∑ i ∈ s, v i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt s u v
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have e1 : (∑ i ∈ s, (u i + v i) ^ 2) =
      ∑ i ∈ s, u i ^ 2 + 2 * ∑ i ∈ s, u i * v i + ∑ i ∈ s, v i ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1]
  have e2 := Real.sq_sqrt hu
  have e3 := Real.sq_sqrt hv
  nlinarith

theorem solution {X : Type*} {d n : ℕ} (Pol : Set (X → Fin d))
    (x : Fin n → X) (γ : Fin n → Fin d → ℝ) (π₁ π₂ π₃ : X → Fin d)
    (h₁ : π₁ ∈ Pol) (h₂ : π₂ ∈ Pol) (h₃ : π₃ ∈ Pol) :
    innerProdDist Pol x γ π₁ π₂ ≤ innerProdDist Pol x γ π₁ π₃ + innerProdDist Pol x γ π₃ π₂ := by
  unfold innerProdDist
  set D : ℝ := ⨆ πa : Pol, ⨆ πb : Pol, ∑ i, (γ i (πa.1 (x i)) - γ i (πb.1 (x i))) ^ 2 with hD
  have hD0 : 0 ≤ D := by
    apply Real.iSup_nonneg; intro a
    apply Real.iSup_nonneg; intro b
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [Real.sqrt_div' _ hD0, Real.sqrt_div' _ hD0, Real.sqrt_div' _ hD0, ← add_div]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg D)
  have := jj_mink Finset.univ (fun i => γ i (π₁ (x i)) - γ i (π₃ (x i)))
    (fun i => γ i (π₃ (x i)) - γ i (π₂ (x i)))
  simpa using this
