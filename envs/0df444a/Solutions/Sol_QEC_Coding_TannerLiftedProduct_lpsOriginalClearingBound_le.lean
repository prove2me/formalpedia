-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalClearingBound_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:57:59.518274+00:00
-- url     : https://prove2.me/submissions/bc4356a9-4ae1-495a-a649-1a3fa88e309e

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.PowerSeries.Expand
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (P : Polynomial (Polynomial ℂ))
    {k i : ℕ} (hk : k∈P.support) (hi : i∈(P.coeff k).support) :
    i+N*k≤lpsOriginalClearingBound N P :=
by
  change i+N*k≤P.support.sup (fun k=>(P.coeff k).support.sup (fun i=>i+N*k))
  have h : i+N*k≤(P.coeff k).support.sup (fun i=>i+N*k) := Finset.le_sup (f := fun i=>i+N*k) hi
  exact h.trans (Finset.le_sup (f := fun k=>(P.coeff k).support.sup (fun i=>i+N*k)) hk)
end QEC.Coding.TannerLiftedProduct
