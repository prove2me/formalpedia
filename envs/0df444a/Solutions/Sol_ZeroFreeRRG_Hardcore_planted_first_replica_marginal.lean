-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.planted_first_replica_marginal
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:08:18.366584+00:00
-- url     : https://prove2.me/submissions/1fbbdc10-6d2e-4353-ac86-a2ee6ea47eb5

import Theorems.Thm_ZeroFreeRRG_Hardcore_gibbs_weights_sum_one
import Mathlib
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (m : Model) (hm : m.Valid) (t s : ℝ) (ht : m.PosParam t) (d n : ℕ)
    (f : Matching n d → (Fin n → m.Spin) → Finset (Fin n) → ℝ) :
    (∑ M : Matching n d, ∑ σ : Fin n → m.Spin, ∑ σ' : Fin n → m.Spin, ∑ U : Finset (Fin n),
      planted m t M σ * gibbs m t M σ' * revealProb s U * f M σ U) =
        plantedPinnedE m t s d n f := by
  classical
  unfold plantedPinnedE
  apply Finset.sum_congr rfl
  intro M hM
  apply Finset.sum_congr rfl
  intro σ hσ
  calc
    _ = ∑ σ' : Fin n → m.Spin, ∑ U : Finset (Fin n),
        (gibbs m t M σ' * (planted m t M σ * revealProb s U * f M σ U)) := by
      apply Finset.sum_congr rfl
      intro σ' hσ'
      apply Finset.sum_congr rfl
      intro U hU
      ring
    _ = ∑ U : Finset (Fin n), ∑ σ' : Fin n → m.Spin,
        (gibbs m t M σ' * (planted m t M σ * revealProb s U * f M σ U)) := Finset.sum_comm
    _ = ∑ U : Finset (Fin n), planted m t M σ * revealProb s U * f M σ U := by
      apply Finset.sum_congr rfl
      intro U hU
      rw [← Finset.sum_mul, gibbs_weights_sum_one m hm t ht d n M,one_mul]
