-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.MeromorphicGerms.normalizedGermValue_mul_analyticUnit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:57:48.774603+00:00
-- url     : https://prove2.me/submissions/8ac948fb-f4c6-4761-b1ba-b5c26b4ec206

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicManifoldNormalForm
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_NormalizedGermUnits
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_normalizedGermValue_eventuallyEq


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open Filter Topology
open scoped Manifold ContDiff
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.MeromorphicGerms
theorem _root_.solution
    (f u : ℂ → ℂ) (x : ℂ) (hf : MeromorphicAt f x)
    (hu : AnalyticAt ℂ u x) (hunit : u x ≠ 0) :
    toMeromorphicNFAt (f * u) x x = toMeromorphicNFAt f x x * u x := by
  have hn : MeromorphicNFAt (toMeromorphicNFAt f x * u) x :=
    (meromorphicNFAt_mul_iff_left hu hunit).mpr meromorphicNFAt_toMeromorphicNFAt
  have he : (f * u) =ᶠ[𝓝[≠] x] (toMeromorphicNFAt f x * u) := by
    filter_upwards [hf.eq_nhdsNE_toMeromorphicNFAt] with z hz
    exact congrArg (fun t : ℂ => t * u z) hz
  have hv := normalizedGermValue_eventuallyEq (f * u) (toMeromorphicNFAt f x * u) x he
  rw [toMeromorphicNFAt_eq_self.mpr hn] at hv
  exact hv
end QEC.Coding.AlgebraicGeometry.MeromorphicGerms
