-- Prove2me | solution 1 for StatComplexityDM.HellingerChain.hellingerSq_convex_right
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:44:19.579748+00:00
-- url     : https://prove2.me/submissions/bff962fa-9757-4a24-9b93-1428487a2206

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Divergences

set_option autoImplicit false
open FoundationsRL.GeneralDM

theorem solution {Y : Type*} [Fintype Y] (Q P Q' : Y → ℝ)
    (hQ : (∀ y, 0 ≤ Q y) ∧ ∑ y, Q y = 1) (hP : (∀ y, 0 ≤ P y) ∧ ∑ y, P y = 1)
    (hQ' : (∀ y, 0 ≤ Q' y) ∧ ∑ y, Q' y = 1) (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    hellingerSq Q ((1 - lam) • P + lam • Q') ≤
      (1 - lam) * hellingerSq Q P + lam * hellingerSq Q Q' := by
  have hpt : ∀ y, (Real.sqrt (Q y) - Real.sqrt (((1 - lam) • P + lam • Q') y)) ^ 2 ≤
      (1 - lam) * (Real.sqrt (Q y) - Real.sqrt (P y)) ^ 2 +
        lam * (Real.sqrt (Q y) - Real.sqrt (Q' y)) ^ 2 := by
    intro y
    have hM : ((1 - lam) • P + lam • Q') y = (1 - lam) * P y + lam * Q' y := by
      simp [Pi.add_apply, smul_eq_mul]
    rw [hM]
    have hconc : (1 - lam) * Real.sqrt (P y) + lam * Real.sqrt (Q' y) ≤
        Real.sqrt ((1 - lam) * P y + lam * Q' y) := by
      have := Real.strictConcaveOn_sqrt.concaveOn.2 (Set.mem_Ici.2 (hP.1 y))
        (Set.mem_Ici.2 (hQ'.1 y)) (sub_nonneg.2 hlam1) hlam0 (by ring)
      simpa [smul_eq_mul] using this
    have hMn : 0 ≤ (1 - lam) * P y + lam * Q' y :=
      add_nonneg (mul_nonneg (sub_nonneg.2 hlam1) (hP.1 y)) (mul_nonneg hlam0 (hQ'.1 y))
    have s1 := Real.sq_sqrt (hQ.1 y)
    have s2 := Real.sq_sqrt (hP.1 y)
    have s3 := Real.sq_sqrt (hQ'.1 y)
    have s4 := Real.sq_sqrt hMn
    have := mul_le_mul_of_nonneg_left hconc (Real.sqrt_nonneg (Q y))
    nlinarith [this, s1, s2, s3, s4]
  unfold hellingerSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun y _ => hpt y
