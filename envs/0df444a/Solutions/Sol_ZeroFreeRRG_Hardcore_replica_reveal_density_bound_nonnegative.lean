-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.replica_reveal_density_bound_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:16:49.051757+00:00
-- url     : https://prove2.me/submissions/014bb1a5-306a-4bfc-b402-54aeceb3dccd

import Theorems.Thm_ZeroFreeRRG_Hardcore_replica_reveal_density_bound
import Mathlib
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (m : Model) (t : ℝ) (d n : ℕ) (M : Matching n d)
    (σ σ' : Fin n → m.Spin) (U : Finset (Fin n)) (B : ℝ)
    (hπ : ∀ a, 0 < m.pi t a) (hnonneg : ∀ τ, 0 ≤ gibbs m t M τ)
    (hgood : pinnedLL m t M σ U + pinnedLL m t M σ' U ≤ B) :
    gibbsMarg m t M σ U * gibbsMarg m t M σ' U ≤
      Real.exp B * ((∏ v ∈ U, m.pi t (σ v)) * (∏ v ∈ U, m.pi t (σ' v))) := by
  classical
  have hG : 0 ≤ gibbsMarg m t M σ U := by
    unfold gibbsMarg
    exact Finset.sum_nonneg fun τ hτ => hnonneg τ
  have hG' : 0 ≤ gibbsMarg m t M σ' U := by
    unfold gibbsMarg
    exact Finset.sum_nonneg fun τ hτ => hnonneg τ
  have hR : 0 ≤ Real.exp B * ((∏ v ∈ U, m.pi t (σ v)) * (∏ v ∈ U, m.pi t (σ' v))) := by
    exact (mul_pos (Real.exp_pos B) (mul_pos
      (Finset.prod_pos fun v hv => hπ (σ v)) (Finset.prod_pos fun v hv => hπ (σ' v)))).le
  by_cases hz : gibbsMarg m t M σ U = 0
  · simp [hz,hR]
  by_cases hz' : gibbsMarg m t M σ' U = 0
  · simp [hz',hR]
  exact replica_reveal_density_bound m t d n M σ σ' U B hπ
    (lt_of_le_of_ne hG (Ne.symm hz)) (lt_of_le_of_ne hG' (Ne.symm hz')) hgood
