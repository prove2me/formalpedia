-- Prove2me | solution 1 for SuttonBartoRL.LinearTD.tdA_eq_matrix_form
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T12:16:09.988794+00:00
-- url     : https://prove2.me/submissions/b077b4d1-c7fd-4c9c-87b5-8b823904f01d

import Mathlib
import Definitions.Def_SuttonBartoRL_LinearTD_MDP
import Definitions.Def_SuttonBartoRL_LinearTD_LinearTD

set_option autoImplicit false

open Matrix

open SuttonBartoRL.LinearTD in
theorem bb0edc57_row {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] {d : ℕ}
    (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (X : Matrix S (Fin d) ℝ) (γ : ℝ)
    (s : S) (i j : Fin d) :
    (∑ a, π.prob s a * ∑ s', ∑ r ∈ M.R, M.p s a s' r * (X s i * (X s j - γ * X s' j)))
      = X s i * (X s j - γ * ∑ t, M.policyTrans π s t * X t j) := by
  have h1 : ∀ a, (∑ s', ∑ r ∈ M.R, M.p s a s' r * (X s i * (X s j - γ * X s' j)))
      = X s i * X s j - γ * X s i * ∑ t, M.trans s a t * X t j := by
    intro a
    have hs := M.p_sum s a
    have e : ∀ s', (∑ r ∈ M.R, M.p s a s' r * (X s i * (X s j - γ * X s' j)))
        = X s i * X s j * (∑ r ∈ M.R, M.p s a s' r)
          - γ * X s i * ((∑ r ∈ M.R, M.p s a s' r) * X s' j) := by
      intro s'
      rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun r _ => by ring
    rw [Finset.sum_congr rfl fun s' _ => e s', Finset.sum_sub_distrib, ← Finset.mul_sum, hs,
      ← Finset.mul_sum]
    simp only [MDP.trans, mul_one]
  rw [Finset.sum_congr rfl fun a _ => by rw [h1 a]]
  have h2 : (∑ t, M.policyTrans π s t * X t j)
      = ∑ a, π.prob s a * ∑ t, M.trans s a t * X t j := by
    simp only [MDP.policyTrans, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun t _ => by ring
  rw [h2]
  have hp := π.sum_one s
  have e2 : ∀ a, π.prob s a * (X s i * X s j - γ * X s i * ∑ t, M.trans s a t * X t j)
      = X s i * X s j * π.prob s a - γ * X s i * (π.prob s a * ∑ t, M.trans s a t * X t j) := by
    intro a; ring
  rw [Finset.sum_congr rfl fun a _ => e2 a, Finset.sum_sub_distrib, ← Finset.mul_sum, hp,
    ← Finset.mul_sum]
  ring

open SuttonBartoRL.LinearTD Matrix in
theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] {d : ℕ}
    (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (μ : S → ℝ) (X : Matrix S (Fin d) ℝ) (γ : ℝ) :
    tdA M π μ X γ = Xᵀ * diagonal μ * (1 - γ • M.policyTrans π) * X := by
  have hY : (1 - γ • M.policyTrans π) * X = X - γ • (M.policyTrans π * X) := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, hY]
  ext i j
  rw [Matrix.mul_apply]
  simp only [diagonal_mul]
  simp only [tdA, Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.mul_apply, transpose_apply, Matrix.sub_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [bb0edc57_row M π X γ s i j]
  ring
