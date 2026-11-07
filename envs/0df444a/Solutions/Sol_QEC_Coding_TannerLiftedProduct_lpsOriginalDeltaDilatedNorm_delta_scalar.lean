-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalDeltaDilatedNorm_delta_scalar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:31:35.585343+00:00
-- url     : https://prove2.me/submissions/1cb6770c-3e82-4d66-83f6-476798df812d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalLevelOne_nowherezero_delta_scalar
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDeltaDilatedNorm_ne_zero_apply

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (hN : 0<N) :
    ∃ c : ℂ, c≠0 ∧ ∀ τ : ℍ, lpsOriginalDeltaDilatedNorm N hN τ=
      c*ModularForm.discriminant τ^(Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)) :=
  lpsOriginalLevelOne_nowherezero_delta_scalar _
    (lpsOriginalDeltaDilatedNorm N hN)
    (lpsOriginalDeltaDilatedNorm_ne_zero_apply N hN)
end QEC.Coding.TannerLiftedProduct
