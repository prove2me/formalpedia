-- Prove2me | solution 1 for PrimalDualLDR.RandomRecourse.theorem_2_primal
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T17:17:44.252886+00:00
-- url     : https://prove2.me/submissions/9c96c4b9-9b03-4bf9-ad4a-49c51bbb3e83

import Mathlib
import Definitions.Def_PrimalDualLDR_RandomRecourse_Problems
import Theorems.Thm_PrimalDualLDR_RandomRecourse_proposition_6

open MeasureTheory Matrix

namespace PDLDRThm2Aux

open PrimalDualLDR.RandomRecourse

lemma q_vecMulVec {k : ℕ} (u v ξ : Fin k → ℝ) :
    ξ ⬝ᵥ (vecMulVec u v *ᵥ ξ) = (ξ ⬝ᵥ u) * (v ⬝ᵥ ξ) := by
  rw [vecMulVec_mulVec, op_smul_eq_smul, dotProduct_smul, smul_eq_mul]
  ring

lemma q_transpose {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (ξ : Fin k → ℝ) :
    ξ ⬝ᵥ (Mᵀ *ᵥ ξ) = ξ ⬝ᵥ (M *ᵥ ξ) := dotProduct_transpose_mulVec M ξ ξ

/-- Quadratic form of the symmetrised affine part. -/
lemma q_sym (σ : Setting) (X : Matrix (Fin σ.n) (Fin σ.k) ℝ) (μ : Fin σ.m) (ξ : Fin σ.k → ℝ) :
    ξ ⬝ᵥ (((1 / 2 : ℝ) • (σ.A μ * X + Xᵀ * (σ.A μ)ᵀ)) *ᵥ ξ) = ξ ⬝ᵥ ((σ.A μ * X) *ᵥ ξ) := by
  rw [smul_mulVec, add_mulVec, dotProduct_smul, dotProduct_add, ← transpose_mul, q_transpose,
    smul_eq_mul]
  ring

lemma q_e1b (σ : Setting) (μ : Fin σ.m) (ξ : Fin σ.k → ℝ) (hξ : σ.e1 ⬝ᵥ ξ = 1) :
    ξ ⬝ᵥ (((1 / 2 : ℝ) • (vecMulVec σ.e1 (σ.B μ) + vecMulVec (σ.B μ) σ.e1)) *ᵥ ξ) =
      σ.B μ ⬝ᵥ ξ := by
  rw [smul_mulVec, add_mulVec, dotProduct_smul, dotProduct_add, q_vecMulVec, q_vecMulVec,
    smul_eq_mul, dotProduct_comm ξ σ.e1, hξ, dotProduct_comm ξ (σ.B μ)]
  ring

lemma ae_Xi (σ : Setting) (hσ : σ.Standing) : ∀ᵐ ξ ∂σ.P, ξ ∈ σ.Xi := by
  rw [ae_iff]
  simpa [Set.compl_def] using hσ.2.2.1.2.1

end PDLDRThm2Aux

open PDLDRThm2Aux PrimalDualLDR.RandomRecourse in
theorem solution (σ : Setting) (hσ : σ.Standing) :
    (∀ (X : Matrix (Fin σ.n) (Fin σ.k) ℝ) (S : Fin σ.m → Matrix (Fin σ.k) (Fin σ.k) ℝ)
        (Λ : Matrix (Fin σ.m) (Fin σ.l) ℝ), σ.Feas314 X S Λ → σ.FeasSPu X S) ∧
      σ.valSPu ≤ σ.valSDP314 ∧
      (σ.l = 1 → σ.StrictlyFeasible → σ.valSPu = σ.valSDP314) := by
  -- (a) conservative approximation
  have hA : ∀ (X : Matrix (Fin σ.n) (Fin σ.k) ℝ) (S : Fin σ.m → Matrix (Fin σ.k) (Fin σ.k) ℝ)
      (Λ : Matrix (Fin σ.m) (Fin σ.l) ℝ), σ.Feas314 X S Λ → σ.FeasSPu X S := by
    rintro X S Λ ⟨hsym, heq, hpsd, hnn⟩
    refine ⟨hsym, fun μ => ?_⟩
    have hnonneg := (proposition_6 σ hσ (S μ) (hsym μ)).1 ⟨Λ μ, hnn μ, hpsd μ⟩
    filter_upwards [hnonneg, ae_Xi σ hσ] with ξ h1 hξ
    refine ⟨?_, h1⟩
    have h := congrArg (fun M => ξ ⬝ᵥ (M *ᵥ ξ)) (heq μ)
    rw [add_mulVec, dotProduct_add, q_sym, q_e1b σ μ ξ hξ.1] at h
    exact h
  -- (b) value inequality
  have hB : σ.valSPu ≤ σ.valSDP314 := by
    unfold Setting.valSDP314
    refine le_iInf₂ (fun p hp => ?_)
    exact iInf₂_le (⟨p.1, p.2.1⟩ : Matrix (Fin σ.n) (Fin σ.k) ℝ ×
      (Fin σ.m → Matrix (Fin σ.k) (Fin σ.k) ℝ)) (hA p.1 p.2.1 p.2.2 hp)
  refine ⟨hA, hB, fun hl _ => le_antisymm hB ?_⟩
  -- (c) exactness for l = 1
  unfold Setting.valSPu
  refine le_iInf₂ (fun p hp => ?_)
  obtain ⟨X, S⟩ := p
  obtain ⟨_, hfe⟩ := hp
  let S' : Fin σ.m → Matrix (Fin σ.k) (Fin σ.k) ℝ := fun μ =>
    (1 / 2 : ℝ) • (vecMulVec σ.e1 (σ.B μ) + vecMulVec (σ.B μ) σ.e1) -
      (1 / 2 : ℝ) • (σ.A μ * X + Xᵀ * (σ.A μ)ᵀ)
  have hS'sym : ∀ μ, (S' μ).IsSymm := by
    intro μ
    show (S' μ)ᵀ = S' μ
    simp only [S', transpose_sub, transpose_smul, transpose_add, transpose_vecMulVec,
      transpose_mul, transpose_transpose]
    abel
  have hS'nn : ∀ μ, ∀ᵐ ξ ∂σ.P, 0 ≤ ξ ⬝ᵥ (S' μ *ᵥ ξ) := by
    intro μ
    filter_upwards [hfe μ, ae_Xi σ hσ] with ξ h hξ
    simp only [S']
    rw [sub_mulVec, dotProduct_sub, q_sym, q_e1b σ μ ξ hξ.1]
    linarith [h.1, h.2]
  have hlam : ∀ μ, ∃ lam : Fin σ.l → ℝ, (∀ ℓ, 0 ≤ lam ℓ) ∧
      (S' μ - ∑ ℓ : Fin σ.l, lam ℓ • σ.W ℓ).PosSemidef :=
    fun μ => (proposition_6 σ hσ (S' μ) (hS'sym μ)).2 hl (hS'nn μ)
  choose Λ hΛnn hΛpsd using hlam
  have hfeas : σ.Feas314 X S' (Matrix.of fun μ ℓ => Λ μ ℓ) := by
    refine ⟨hS'sym, fun μ => ?_, fun μ => hΛpsd μ, fun μ ℓ => hΛnn μ ℓ⟩
    simp only [S']
    abel
  exact iInf₂_le (⟨X, S', Matrix.of fun μ ℓ => Λ μ ℓ⟩ : Matrix (Fin σ.n) (Fin σ.k) ℝ ×
      (Fin σ.m → Matrix (Fin σ.k) (Fin σ.k) ℝ) × Matrix (Fin σ.m) (Fin σ.l) ℝ) hfeas
