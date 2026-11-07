-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalHolomorphicCoefficientDerivative_germ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:50:49.110439+00:00
-- url     : https://prove2.me/submissions/40cdbab0-e749-4db6-8194-e3006c02ca16

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicGerms
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.MeanValue
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDifferentiation

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane Manifold
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (f : LPSOriginalHolomorphicRing) :
    lpsOriginalHolomorphicToMeromorphicGerm (lpsOriginalHolomorphicCoefficientDerivative f) =
      lpsOriginalMeromorphicGermCoefficientDerivative UpperHalfPlane.upperHalfPlaneSet
        (lpsOriginalHolomorphicToMeromorphicGerm f) := by
  apply Subtype.ext
  rw [lpsOriginalMeromorphicGermCoefficientDerivative_value _ _
    (f.val ∘ UpperHalfPlane.ofComplex) (lpsOriginalHolomorphic_ofComplex_meromorphic f) rfl]
  apply Filter.Germ.coe_eq.mpr
  rw [Filter.EventuallyEq, Filter.Eventually, mem_codiscreteWithin_iff_forall_mem_nhdsNE]
  intro z hz
  filter_upwards [nhdsWithin_le_nhds
    (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hz)] with w hw
  exact Or.inl (by
    change deriv (f.val ∘ UpperHalfPlane.ofComplex)
      (UpperHalfPlane.ofComplex w : ℂ) = deriv (f.val ∘ UpperHalfPlane.ofComplex) w
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hw])
end QEC.Coding.TannerLiftedProduct
