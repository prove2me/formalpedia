-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledForgetLevel_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:22:46.336627+00:00
-- url     : https://prove2.me/submissions/3c6106e0-6734-440a-8f9d-f0bd65648e62

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Mathlib.Topology.Maps.Proper.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelMapGeometry
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInteriorForgetLevel_continuous
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledForgetLevel_cuspChart_continuousOn
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_interior_continuous
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_isOpen_iff


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledTopology M
    Continuous (lpsOriginalFilledForgetLevel N M hNM) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledTopology M
  apply continuous_def.mpr
  intro s hs
  apply (lpsOriginalFilledTopology_isOpen_iff M
    ((lpsOriginalFilledForgetLevel N M hNM) ⁻¹' s)).mpr
  constructor
  · have hi : Continuous (fun y => Sum.inl (lpsOriginalInteriorForgetLevel N M hNM y)) :=
      (lpsOriginalFilledTopology_interior_continuous N).comp
        (lpsOriginalInteriorForgetLevel_continuous N M hNM)
    change IsOpen ((fun y => Sum.inl (lpsOriginalInteriorForgetLevel N M hNM y)) ⁻¹' s)
    exact hi.isOpen_preimage s hs
  · intro c
    have hc : Continuous (fun q : (lpsOriginalFilledCuspChart M c).target =>
      lpsOriginalFilledForgetLevel N M hNM ((lpsOriginalFilledCuspChart M c).symm q.val)) :=
      continuousOn_iff_continuous_domRestrict.mp
        (lpsOriginalFilledForgetLevel_cuspChart_continuousOn N M hNM c)
    change IsOpen ((fun q : (lpsOriginalFilledCuspChart M c).target =>
      lpsOriginalFilledForgetLevel N M hNM ((lpsOriginalFilledCuspChart M c).symm q.val)) ⁻¹' s)
    exact hc.isOpen_preimage s hs
end QEC.Coding.TannerLiftedProduct
