-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.MeromorphicGerms.normalizedGermValue_comp_mul_analyticUnit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:24:08.636087+00:00
-- url     : https://prove2.me/submissions/bde9d8c4-7e24-4344-bafc-ca7e518605bd

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicManifoldNormalForm
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_NormalizedGermUnits
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_normalizedGermValue_mul_analyticUnit
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_normalizedGermValue_comp


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open Filter Topology
open scoped Manifold ContDiff
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.MeromorphicGerms
theorem _root_.solution
    (f g u : ℂ → ℂ) (x : ℂ) (hf : MeromorphicAt f (g x))
    (hg : AnalyticAt ℂ g x) (hu : AnalyticAt ℂ u x) (hunit : u x ≠ 0)
    (ht : Tendsto g (𝓝[≠] x) (𝓝[≠] (g x))) :
    toMeromorphicNFAt ((f ∘ g) * u) x x =
      toMeromorphicNFAt f (g x) (g x) * u x := by
  rw [normalizedGermValue_mul_analyticUnit (f ∘ g) u x
    (hf.comp_analyticAt hg) hu hunit,
    normalizedGermValue_comp f g x hf hg ht]
end QEC.Coding.AlgebraicGeometry.MeromorphicGerms
