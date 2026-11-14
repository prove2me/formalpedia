-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.replica_likelihood_tail
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:12:40.8972+00:00
-- url     : https://prove2.me/submissions/dc703922-5c28-4fba-ab16-592d3ea7fa2c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_ZeroFreeRRG_Hardcore_replica_likelihood_union_bound
import Theorems.Thm_ZeroFreeRRG_Hardcore_overlap_pinned_likelihood_tail
import Mathlib
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (m : Model) (hm : m.Valid) (d : ℕ) (hd : 3 ≤ d) (t : ℝ) (ht : m.PosParam t)
    (hC1 : Condition1 m d t) (η : ℝ) (hη : 0 < η) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ,
      ∀ n ≥ N, Even (n*d) →
      (∑ M : Matching n d, ∑ σ : Fin n → m.Spin, ∑ σ' : Fin n → m.Spin, ∑ U : Finset (Fin n),
        planted m t M σ * gibbs m t M σ' * revealProb s U *
          (if pinnedLL m t M σ U + pinnedLL m t M σ' U > (s*η^2/24)*n then 1 else 0)) ≤
        2*Real.exp (-c*n) := by
  classical
  obtain ⟨s,hs,hs1,c,hc,N,hN⟩ := overlap_pinned_likelihood_tail m hm d hd t ht hC1 η hη
  refine ⟨s,hs,hs1,c,hc,N,?_⟩
  intro n hn heven
  have hu := replica_likelihood_union_bound m hm t s ht hs.le hs1.le d n ((s*η^2/48)*n)
  have ht' := hN n hn heven
  have heq : 2*((s*η^2/48)*n) = (s*η^2/24)*n := by ring
  rw [heq] at hu
  exact hu.trans (mul_le_mul_of_nonneg_left ht' (by norm_num))
