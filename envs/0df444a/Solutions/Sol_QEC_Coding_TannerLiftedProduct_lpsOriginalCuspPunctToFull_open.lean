-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspPunctToFull_open
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:45:48.116787+00:00
-- url     : https://prove2.me/submissions/92e201e6-0540-4022-bc19-2e094b8db712

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspPartialEquiv_target_open

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    IsOpenMap (lpsOriginalCuspPunctToFull N ρ) := by
  have hd := lpsOriginalFilledCuspPartialEquiv_target_open N ρ
  have hp : IsOpen (lpsOriginalCuspDisk N ρ) :=
    (isOpen_ne_fun continuous_id continuous_const).inter
      (isOpen_lt continuous_norm continuous_const)
  exact hd.isOpenEmbedding_subtypeVal.isOpenMap_iff.mpr hp.isOpenMap_subtype_val
end QEC.Coding.TannerLiftedProduct
