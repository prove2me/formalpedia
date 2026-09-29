-- Prove2me | solution 1 for OnlineConvexOpt.GamesDuality.weak_duality
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T04:14:33.884868+00:00
-- url     : https://prove2.me/submissions/64bd83ad-520a-4133-9b11-02b069f617db

import Mathlib
import Definitions.Def_OnlineConvexOpt_GamesDuality_Game

set_option autoImplicit false

theorem gd_zero_not_mem_stdSimplex (k : ℕ) : (0 : Fin k → ℝ) ∉ stdSimplex ℝ (Fin k) := by
  intro h
  have h1 := h.2
  simp at h1

open OnlineConvexOpt.GamesDuality in
theorem solution {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (A : Matrix (Fin n) (Fin m) ℝ) :
    lambdaC A ≤ lambdaR A := by
  have hC : lambdaC A ≤ 0 := by
    unfold lambdaC
    refine Real.iSup_nonpos (fun y => Real.iSup_nonpos (fun _ => ?_))
    refine Real.iInf_nonpos' ⟨0, ?_⟩
    rw [ciInf_neg (gd_zero_not_mem_stdSimplex n), Real.sInf_empty]
  have hR : 0 ≤ lambdaR A := by
    unfold lambdaR
    refine Real.iInf_nonneg (fun x => Real.iInf_nonneg (fun _ => ?_))
    refine Real.iSup_nonneg' ⟨0, ?_⟩
    rw [ciSup_neg (gd_zero_not_mem_stdSimplex m), Real.sSup_empty]
  linarith
