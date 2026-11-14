-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.replica_reveal_density_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:12:40.954649+00:00
-- url     : https://prove2.me/submissions/0320ff7e-16c4-4f87-a05c-ea646d0f0225

import Theorems.Thm_ZeroFreeRRG_Hardcore_pinned_likelihood_density
import Mathlib
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (m : Model) (t : ℝ) (d n : ℕ) (M : Matching n d)
    (σ σ' : Fin n → m.Spin) (U : Finset (Fin n)) (B : ℝ)
    (hπ : ∀ a, 0 < m.pi t a)
    (hG : 0 < gibbsMarg m t M σ U) (hG' : 0 < gibbsMarg m t M σ' U)
    (hgood : pinnedLL m t M σ U + pinnedLL m t M σ' U ≤ B) :
    gibbsMarg m t M σ U * gibbsMarg m t M σ' U ≤
      Real.exp B * ((∏ v ∈ U, m.pi t (σ v)) * (∏ v ∈ U, m.pi t (σ' v))) := by
  classical
  have hp : 0 < ∏ v ∈ U, m.pi t (σ v) := Finset.prod_pos fun v hv => hπ (σ v)
  have hp' : 0 < ∏ v ∈ U, m.pi t (σ' v) := Finset.prod_pos fun v hv => hπ (σ' v)
  have h := Real.exp_le_exp.mpr hgood
  rw [Real.exp_add, pinned_likelihood_density m t d n M σ U hπ hG,
    pinned_likelihood_density m t d n M σ' U hπ hG'] at h
  have heq : (gibbsMarg m t M σ U / ∏ v ∈ U, m.pi t (σ v)) *
      (gibbsMarg m t M σ' U / ∏ v ∈ U, m.pi t (σ' v)) =
    (gibbsMarg m t M σ U * gibbsMarg m t M σ' U) /
      ((∏ v ∈ U, m.pi t (σ v)) * (∏ v ∈ U, m.pi t (σ' v))) := by ring
  rw [heq] at h
  exact (div_le_iff₀ (mul_pos hp hp')).mp h
