-- Prove2me | solution 1 for SuttonBartoRL.LinearTD.keyMatrix_colSums
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T09:25:18.325059+00:00
-- url     : https://prove2.me/submissions/37d13939-a1ad-4e6a-98d6-cfd546a50943

import Mathlib
import Definitions.Def_SuttonBartoRL_LinearTD_MDP
import Definitions.Def_SuttonBartoRL_LinearTD_LinearTD

open Matrix

open Matrix SuttonBartoRL.LinearTD in
theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (μ : S → ℝ) (γ : ℝ)
    (hγ1 : γ < 1) (hμpos : ∀ s, 0 < μ s) (hstat : vecMul μ (M.policyTrans π) = μ) :
    vecMul (fun _ => (1 : ℝ)) (keyMatrix μ (M.policyTrans π) γ) = (1 - γ) • μ ∧
      ∀ s, 0 < vecMul (fun _ => (1 : ℝ)) (keyMatrix μ (M.policyTrans π) γ) s := by
  have key : vecMul (fun _ => (1 : ℝ)) (keyMatrix μ (M.policyTrans π) γ) = (1 - γ) • μ := by
    have h1 : vecMul (fun _ => (1 : ℝ)) (diagonal μ) = μ := by
      funext x; rw [vecMul_diagonal]; simp
    unfold keyMatrix
    rw [← vecMul_vecMul, h1, vecMul_sub, vecMul_one, vecMul_smul, hstat, sub_smul, one_smul]
  refine ⟨key, fun s => ?_⟩
  rw [key, Pi.smul_apply, smul_eq_mul]
  exact mul_pos (by linarith) (hμpos s)
