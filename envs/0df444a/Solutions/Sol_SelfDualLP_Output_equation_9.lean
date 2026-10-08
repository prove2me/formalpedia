-- Prove2me | solution 1 for SelfDualLP.Output.equation_9
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T22:35:57.963923+00:00
-- url     : https://prove2.me/submissions/d4e76a8d-b832-4e2a-a252-198eff63aaac

import Mathlib
import Definitions.Def_SelfDualLP_Complexity_LPData
import Definitions.Def_SelfDualLP_Output_HLP
import Definitions.Def_SelfDualLP_Output_Neighborhood
import Definitions.Def_SelfDualLP_Output_PCSequence

open Matrix
open SelfDualLP.Output
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (z : HLPPoint m n) (hz : HLPFeasible7 A b c z) :
    ones n ⬝ᵥ z.x + ones n ⬝ᵥ z.s + z.τ + z.κ - ((n : ℝ) + 1) * z.θ = (n : ℝ) + 1 := by
  rcases hz with ⟨h1, h2, h3, h4, hx, ht, hs, hk⟩
  have h2' := congrArg (fun v => ones n ⬝ᵥ v) h2
  simp only [cbar, zbar, bbar, Matrix.mulVec_zero, sub_zero,
    dotProduct_sub, dotProduct_add, dotProduct_neg, dotProduct_smul,
    dotProduct_zero, smul_dotProduct] at h2' h3 h4
  have he : ones n ⬝ᵥ ones n = (n : ℝ) := by simp [ones, dotProduct]
  rw [he] at h2' h4
  have hA : ones n ⬝ᵥ (Aᵀ *ᵥ z.y) = (A *ᵥ ones n) ⬝ᵥ z.y := by
    rw [dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
  rw [hA] at h2'
  have hc : ones n ⬝ᵥ c = c ⬝ᵥ ones n := dotProduct_comm _ _
  simp only [sub_dotProduct, smul_eq_mul] at h2' h4
  rw [hc] at h2'
  nlinarith
#print axioms solution
