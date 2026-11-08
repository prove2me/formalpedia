-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalModularNorm_polynomial_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:08:45.584083+00:00
-- url     : https://prove2.me/submissions/55e72e1c-dabd-4891-8646-621d344a0eb8

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPolynomial
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Lagrange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModularNorm_nonzero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass MatrixGroups
open scoped ModularForm UpperHalfPlane
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (hN : 0<N) (c : ℂ) :
    ∃ P : Polynomial ℂ, P≠0 ∧
      P.natDegree≤Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) ∧
      ∀ τ : ℍ, lpsOriginalModularNorm N hN c τ=
        ModularForm.discriminant τ^(Nat.card (𝒮ℒ ⧸
          (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ))*
          P.eval (lpsOriginalJInvariant τ) := by
  obtain ⟨P,⟨hP,hPeval⟩,_⟩ := lpsOriginalModularNorm_unique_polynomial N hN c
  refine ⟨P,?_,hP,hPeval⟩
  intro hzero
  apply lpsOriginalModularNorm_nonzero N hN c
  ext τ
  rw [hPeval τ,hzero,Polynomial.eval_zero,mul_zero]
  rfl
end QEC.Coding.TannerLiftedProduct
