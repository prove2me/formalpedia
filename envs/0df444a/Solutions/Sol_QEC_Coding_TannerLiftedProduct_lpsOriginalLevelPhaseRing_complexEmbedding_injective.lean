-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalLevelPhaseRing_complexEmbedding_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:38:42.496959+00:00
-- url     : https://prove2.me/submissions/d2a1ad81-f3f5-470e-a931-99cdf66edcbf

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCosetCuspSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCoprimeModularReduction

set_option autoImplicit false
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalLevelPhasePrime_isMaximal
attribute [local instance] lpsOriginalLevelPhaseResidue_field
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) :
    Function.Injective (lpsOriginalLevelPhaseRing N).val.toRingHom := by
  intro x y hxy
  exact Subtype.ext hxy
end QEC.Coding.TannerLiftedProduct
