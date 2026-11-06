-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.MeromorphicGerms.normalizedGermValue_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:56:46.383632+00:00
-- url     : https://prove2.me/submissions/1fd8b21a-7da2-40ac-ac05-0d7f597068fe

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
    (hf : MeromorphicAt f (g x)) (hg : AnalyticAt ℂ g x)
    (ht : Tendsto g (𝓝[≠] x) (𝓝[≠] (g x))) :
    toMeromorphicNFAt (f ∘ g) x x = toMeromorphicNFAt f (g x) (g x) := by
  have hcomp := hf.comp_analyticAt hg
  have hn₁ : MeromorphicNFAt (toMeromorphicNFAt (f ∘ g) x) x :=
    meromorphicNFAt_toMeromorphicNFAt
  have hn₂ : MeromorphicNFAt (toMeromorphicNFAt f (g x) ∘ g) x :=
    (meromorphicNFAt_toMeromorphicNFAt (f := f) (x := g x)).comp_analyticAt hg
  have he : (f ∘ g) =ᶠ[𝓝[≠] x] (toMeromorphicNFAt f (g x) ∘ g) :=
    ht.eventually hf.eq_nhdsNE_toMeromorphicNFAt
  exact ((hn₁.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hn₂).mp
    (hcomp.eq_nhdsNE_toMeromorphicNFAt.symm.trans he)).eq_of_nhds
end QEC.Coding.AlgebraicGeometry.MeromorphicGerms
