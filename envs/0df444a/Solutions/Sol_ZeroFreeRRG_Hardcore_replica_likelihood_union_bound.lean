-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.replica_likelihood_union_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:08:43.90367+00:00
-- url     : https://prove2.me/submissions/35ee823e-05ab-40eb-b374-6e44fb8c24bf

import Theorems.Thm_ZeroFreeRRG_Hardcore_planted_first_replica_marginal
import Theorems.Thm_ZeroFreeRRG_Hardcore_planted_second_replica_marginal
import Theorems.Thm_ZeroFreeRRG_Hardcore_planted_replica_reveal_weight_nonnegative
import Mathlib
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (m : Model) (hm : m.Valid) (t s : ℝ) (ht : m.PosParam t)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (d n : ℕ) (B : ℝ) :
    (∑ M : Matching n d, ∑ σ : Fin n → m.Spin, ∑ σ' : Fin n → m.Spin, ∑ U : Finset (Fin n),
      planted m t M σ * gibbs m t M σ' * revealProb s U *
        (if pinnedLL m t M σ U + pinnedLL m t M σ' U > 2*B then 1 else 0)) ≤
    2 * plantedPinnedE m t s d n (fun M σ U => if pinnedLL m t M σ U > B then 1 else 0) := by
  classical
  let f := fun (M : Matching n d) (σ : Fin n → m.Spin) (U : Finset (Fin n)) =>
    if pinnedLL m t M σ U > B then (1:ℝ) else 0
  have hp := planted_replica_reveal_weight_nonnegative m hm t s ht hs hs1 d n
  have hsum : (∑ M : Matching n d, ∑ σ : Fin n → m.Spin, ∑ σ' : Fin n → m.Spin, ∑ U : Finset (Fin n),
      planted m t M σ * gibbs m t M σ' * revealProb s U *
        (if pinnedLL m t M σ U + pinnedLL m t M σ' U > 2*B then 1 else 0)) ≤
    (∑ M : Matching n d, ∑ σ : Fin n → m.Spin, ∑ σ' : Fin n → m.Spin, ∑ U : Finset (Fin n),
      planted m t M σ * gibbs m t M σ' * revealProb s U * (f M σ U + f M σ' U)) := by
    apply Finset.sum_le_sum
    intro M hM
    apply Finset.sum_le_sum
    intro σ hσ
    apply Finset.sum_le_sum
    intro σ' hσ'
    apply Finset.sum_le_sum
    intro U hU
    apply mul_le_mul_of_nonneg_left _ (hp M σ σ' U)
    dsimp [f]
    split_ifs <;> norm_num at * <;> linarith
  simp only [mul_add,Finset.sum_add_distrib] at hsum
  have hfirst := planted_first_replica_marginal m hm t s ht d n f
  have hsecond := planted_second_replica_marginal m hm t s ht d n f
  rw [hfirst,hsecond] at hsum
  dsimp [f] at hsum
  linarith
