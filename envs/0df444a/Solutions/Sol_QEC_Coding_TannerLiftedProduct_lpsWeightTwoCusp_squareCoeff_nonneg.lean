-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsWeightTwoCusp_squareCoeff_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:42:38.27639+00:00
-- url     : https://prove2.me/submissions/48c70f86-c482-45b9-b0bc-a3f891d46ff9

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspSquareLSeries

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (n : ℕ) :
    0≤lpsWeightTwoCusp_squareCoeff N f n := sq_nonneg _
end QEC.Coding.TannerLiftedProduct
