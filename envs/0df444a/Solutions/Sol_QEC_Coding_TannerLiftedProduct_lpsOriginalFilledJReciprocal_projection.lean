-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJReciprocal_projection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:13:02.080204+00:00
-- url     : https://prove2.me/submissions/19c4e92e-0295-4499-8ff6-2e8063491028

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (a : ℂ) (τ : ℍ) :
    lpsOriginalFilledJReciprocal N a (Sum.inl ⟦τ⟧)=(lpsOriginalJInvariant τ-a)⁻¹ := rfl
end QEC.Coding.TannerLiftedProduct
