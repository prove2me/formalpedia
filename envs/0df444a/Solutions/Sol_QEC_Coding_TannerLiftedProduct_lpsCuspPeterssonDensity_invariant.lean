-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonDensity_invariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:10:27.143208+00:00
-- url     : https://prove2.me/submissions/1506abb7-bce7-4aa4-afdd-980c3bb7bbda

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonTrace_invariant

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (h : SL(2,ℤ)) (τ : ℍ) :
    lpsCuspPeterssonDensity N f (h • τ)=lpsCuspPeterssonDensity N f τ := by
  exact congrArg Complex.re (lpsCuspPeterssonTrace_invariant N f f h τ)
end QEC.Coding.TannerLiftedProduct
