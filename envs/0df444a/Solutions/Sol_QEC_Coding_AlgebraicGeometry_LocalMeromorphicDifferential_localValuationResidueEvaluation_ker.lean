-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.localValuationResidueEvaluation_ker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:09:32.614206+00:00
-- url     : https://prove2.me/submissions/cf09f3ed-a644-4386-a032-ea7de5824a60

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalKaehlerCyclic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_LocalMeromorphicDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AnalyticGermEvaluation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicValuationDifferentials
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_meromorphicNoPoleEvaluation_eq_zero_iff_order_pos


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
noncomputable section
variable (K : Type*) [Field K] [Algebra ℂ K] (a : ℂ)
attribute [local instance] QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.MeromorphicValuationDifferentialsDictionary001
variable [Algebra K (MeromorphicGermRing a)] [IsScalarTower ℂ K (MeromorphicGermRing a)]
local notation "V" => localValuationRing K a
attribute [local instance] QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.MeromorphicValuationDifferentialsDictionary002
attribute [local instance] QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.MeromorphicValuationDifferentialsDictionary003
namespace QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential
theorem _root_.solution :
    RingHom.ker (localValuationResidueEvaluation K a) = IsLocalRing.maximalIdeal V := by
  ext t
  rw [RingHom.mem_ker, (AddValuation.toValuation (localFieldOrder K a)).mem_maximalIdeal_iff]
  change meromorphicNoPoleEvaluation a (localValuationToMeromorphicInteger K a t) = 0 ↔
    0 < meromorphicOrderValuation a (algebraMap K (MeromorphicGermRing a) t.val)
  exact meromorphicNoPoleEvaluation_eq_zero_iff_order_pos a _
end QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential
