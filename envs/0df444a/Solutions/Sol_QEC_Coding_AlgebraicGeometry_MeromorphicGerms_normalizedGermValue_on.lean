-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.MeromorphicGerms.normalizedGermValue_on
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:57:17.855069+00:00
-- url     : https://prove2.me/submissions/3d7b49d0-271c-4425-af57-10971e7b30c9

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
theorem _root_.solution (f : ℂ → ℂ) (U : Set ℂ) (x : ℂ)
    (hf : MeromorphicOn f U) (hx : x ∈ U) :
    toMeromorphicNFOn f U x = toMeromorphicNFAt f x x :=
  toMeromorphicNFOn_eq_toMeromorphicNFAt hf hx
end QEC.Coding.AlgebraicGeometry.MeromorphicGerms
