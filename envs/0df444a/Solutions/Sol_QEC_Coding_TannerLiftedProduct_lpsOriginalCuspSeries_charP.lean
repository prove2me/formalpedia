-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspSeries_charP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:39:36.982954+00:00
-- url     : https://prove2.me/submissions/4dadb116-87ca-4aec-901e-b1327f7ed1d2

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCyclotomicCoefficients
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.Localization.Away.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspSeriesAlgebraMap_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (p : ℕ) [Fact p.Prime] :
    CharP (lpsOriginalCuspSeriesRing (ZMod p)) p := by
  let : CharP (PowerSeries (ZMod p)) p :=
    charP_of_injective_ringHom PowerSeries.C_injective p
  exact charP_of_injective_algebraMap (lpsOriginalCuspSeriesAlgebraMap_injective (ZMod p)) p
end QEC.Coding.TannerLiftedProduct
