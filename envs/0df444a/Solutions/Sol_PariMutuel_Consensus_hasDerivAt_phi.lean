-- Prove2me | solution 1 for PariMutuel.Consensus.hasDerivAt_phi
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T12:20:13.466784+00:00
-- url     : https://prove2.me/submissions/3340994a-a801-4bcd-9410-c8f46b2bb6ad

import Mathlib
import Definitions.Def_PariMutuel_Consensus_Market
import Definitions.Def_PariMutuel_Consensus_Phi



namespace PariMutuel.Consensus

theorem pm_inner_update {m n : ℕ} (M : Market m n) (ξ : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n)
    (t : ℝ) : ∑ s, M.P i s * Function.update (ξ i) j t s
      = ∑ s, M.P i s * ξ i s + M.P i j * (t - ξ i j) := by
  have : ∀ s, M.P i s * Function.update (ξ i) j t s
      = M.P i s * ξ i s + (if s = j then M.P i j * (t - ξ i j) else 0) := by
    intro s
    rw [Function.update_apply]
    split_ifs with h
    · subst h; ring
    · ring
  simp_rw [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem pm_hasDeriv {m n : ℕ} (M : Market m n) (ξ : Fin m → Fin n → ℝ)
    (hξ : ∀ i, 0 < ∑ j, M.P i j * ξ i j) (i : Fin m) (j : Fin n) :
    HasDerivAt (fun t : ℝ => M.phi (Function.update ξ i (Function.update (ξ i) j t)))
      (M.b i * M.P i j / ∑ s, M.P i s * ξ i s) (ξ i j) := by
  unfold Market.phi
  have key : ∀ i' ∈ (Finset.univ : Finset (Fin m)),
      HasDerivAt (fun t : ℝ => M.b i' * Real.log (∑ s, M.P i' s *
        Function.update ξ i (Function.update (ξ i) j t) i' s))
        (if i' = i then M.b i * M.P i j / ∑ s, M.P i s * ξ i s else 0) (ξ i j) := by
    intro i' _
    by_cases hi : i' = i
    · subst hi
      simp only [Function.update_self, if_true, pm_inner_update]
      have h0 := hξ i'
      have := ((((hasDerivAt_id (ξ i' j)).sub_const (ξ i' j)).const_mul (M.P i' j)).const_add
        (∑ s, M.P i' s * ξ i' s)).log (by simp; exact h0.ne')
      have := this.const_mul (M.b i')
      refine this.congr_deriv ?_
      simp
      ring
    · simp only [Function.update_of_ne hi, hi, if_false]
      exact hasDerivAt_const _ _
  have := HasDerivAt.fun_sum key
  refine this.congr_deriv ?_
  rw [Finset.sum_ite_eq']
  simp

end PariMutuel.Consensus

open PariMutuel.Consensus


theorem solution {m n : ℕ} (M : Market m n) (ξ : Fin m → Fin n → ℝ)
    (hξ : ∀ i, 0 < ∑ j, M.P i j * ξ i j) (i : Fin m) (j : Fin n) :
    HasDerivAt (fun t : ℝ => M.phi (Function.update ξ i (Function.update (ξ i) j t)))
      (M.b i * M.P i j / ∑ s, M.P i s * ξ i s) (ξ i j) := by
  exact pm_hasDeriv M ξ hξ i j
