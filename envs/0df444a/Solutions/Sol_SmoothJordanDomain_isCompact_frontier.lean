-- Prove2me | solution 1 for SmoothJordanDomain.isCompact_frontier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:51:57.652788+00:00
-- url     : https://prove2.me/submissions/1103ed3c-1b16-4ebb-8f58-46f2e6b56760

import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_DoubleLayer
import Definitions.Def_Operator_Crouzeix_DoubleLayerIntegral
import Definitions.Def_Operator_Crouzeix_PositiveIntegral
import Definitions.Def_Operator_Crouzeix_ProductContour
import Definitions.Def_Operator_Crouzeix_SymmetrizedAuxiliary
import Definitions.Def_Operator_Crouzeix_SymmetrizedBound
import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized

set_option autoImplicit false
open Complex MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
open SmoothJordanDomain
namespace SmoothJordanDomain
theorem _root_.solution (Omega : SmoothJordanDomain) :
    IsCompact (frontier Omega.carrier) := by
  rw [← Omega.boundaryParam_range]
  exact Omega.boundaryParam_periodic.compact_of_continuous
    (by positivity) Omega.boundaryParam_contDiff.continuous
end SmoothJordanDomain
