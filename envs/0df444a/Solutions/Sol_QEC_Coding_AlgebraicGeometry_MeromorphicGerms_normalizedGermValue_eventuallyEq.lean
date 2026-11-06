-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.MeromorphicGerms.normalizedGermValue_eventuallyEq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:56:49.587798+00:00
-- url     : https://prove2.me/submissions/162ed325-6a78-4924-bb56-3affebcdd363

import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicManifoldNormalForm

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open Filter Topology
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.MeromorphicGerms
theorem _root_.solution (f g : ℂ → ℂ) (x : ℂ)
    (h : f =ᶠ[𝓝[≠] x] g) :
    toMeromorphicNFAt f x x = toMeromorphicNFAt g x x :=
  (toMeromorphicNFAt_eventuallyEq_nhds_congr h).eq_of_nhds
end QEC.Coding.AlgebraicGeometry.MeromorphicGerms
