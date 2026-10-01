-- Prove2me | solution 1 for RobustMDP.Stationarity.stationaryNature_policy_stationary
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T12:05:10.965966+00:00
-- url     : https://prove2.me/submissions/04f9065c-613a-40e8-a71b-4670d20a72f0

import Theorems.Thm_RobustMDP_Stationarity_stationary_policies_suffice
open RobustMDP.Stationarity

theorem solution {n : ℕ} {A : Type} [Fintype A] [Nonempty A]
    (M : Model n A) (ν : ℝ) (hν₀ : 0 < ν) (hν₁ : ν < 1) (i₀ : Fin n) :
    M.phiInf_PTs ν i₀=M.phiInf_PsTs ν i₀ := by
  have h := (stationary_policies_suffice M ν hν₀ hν₁ i₀).1
  exact h.2.2.symm.trans h.2.1.symm
