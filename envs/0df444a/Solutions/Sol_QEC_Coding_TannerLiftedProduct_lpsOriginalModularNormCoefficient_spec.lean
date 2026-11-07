-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalModularNormCoefficient_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:11:40.036548+00:00
-- url     : https://prove2.me/submissions/d70d6e3e-8bec-4b16-867f-10111366dc62

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPolynomial
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Lagrange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass MatrixGroups
open scoped ModularForm UpperHalfPlane
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (hN : 0<N) (c : ℂ) :
    (lpsOriginalModularNormCoefficient N hN c).natDegree≤
      Nat.card (𝒮ℒ ⧸ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) ∧
      ∀ τ : ℍ, lpsOriginalModularNorm N hN c τ=
        ModularForm.discriminant τ^(Nat.card (𝒮ℒ ⧸
          (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ))*
          (lpsOriginalModularNormCoefficient N hN c).eval (lpsOriginalJInvariant τ) :=
  Classical.choose_spec (lpsOriginalModularNorm_unique_polynomial N hN c).exists
end QEC.Coding.TannerLiftedProduct
