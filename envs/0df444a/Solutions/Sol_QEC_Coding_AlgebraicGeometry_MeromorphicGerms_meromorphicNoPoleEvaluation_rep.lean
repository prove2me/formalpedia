-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.MeromorphicGerms.meromorphicNoPoleEvaluation_rep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:04:54.599199+00:00
-- url     : https://prove2.me/submissions/6319a4a6-33ce-43ed-ac35-fe32e00b2ec9

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicGerms
import Mathlib.Topology.Instances.Complex
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AnalyticGermEvaluation

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open Filter Topology
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.MeromorphicGerms
theorem _root_.solution (x : ℂ)
    (A : (AddValuation.toValuation (meromorphicOrderValuation x)).integer)
    (f : ℂ → ℂ) (hf : AnalyticAt ℂ f x)
    (he : A.val.val = (f : Germ (𝓝[≠] x) ℂ)) :
    meromorphicNoPoleEvaluation x A = f x :=
  analyticGermValue_rep x (meromorphicNoPoleToAnalytic x A) f hf he
end QEC.Coding.AlgebraicGeometry.MeromorphicGerms
