-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspGroup_level_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:26:41.595657+00:00
-- url     : https://prove2.me/submissions/b4bf991c-f190-4140-b814-ae8d1a9e087b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N M : ℕ) (hNM : N ∣ M) (ρ : SL(2, ℤ)) :
    lpsOriginalCuspGroup M ρ ≤ lpsOriginalCuspGroup N ρ := by
  intro g hg
  rw [lpsOriginalCuspGroup, ConjAct.toConjAct_inv,
    Subgroup.mem_inv_pointwise_smul_iff, ConjAct.toConjAct_smul] at hg ⊢
  exact (Subgroup.map_mono (lpsGamma0_level_le N M hNM)) hg
end QEC.Coding.TannerLiftedProduct
