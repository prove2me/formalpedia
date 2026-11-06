-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.MeromorphicGerms.meromorphicNoPoleEvaluation_eq_zero_iff_order_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:02:05.790932+00:00
-- url     : https://prove2.me/submissions/0317adf0-b661-431d-9c51-d9a6103bc8f0

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicGerms
import Mathlib.Topology.Instances.Complex
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AnalyticGermEvaluation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_meromorphicNoPoleEvaluation_rep
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_germOrder_coe


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open Filter Topology
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.MeromorphicGerms
theorem _root_.solution
    (x : ℂ) (A : (AddValuation.toValuation (meromorphicOrderValuation x)).integer) :
    meromorphicNoPoleEvaluation x A = 0 ↔ 0 < meromorphicOrderValuation x A.val := by
  have hp : 0 ≤ meromorphicOrderValuation x A.val := A.property
  obtain ⟨f,hf,he⟩ := (meromorphicGerm_noPole_iff_analytic x A.val).mp hp
  rw [meromorphicNoPoleEvaluation_rep x A f hf he]
  change f x = 0 ↔ 0 < germOrder x A.val.val
  rw [he,germOrder_coe]
  have ht : Tendsto f (𝓝[≠] x) (𝓝 (f x)) :=
    hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  constructor
  · intro hz
    exact (tendsto_zero_iff_meromorphicOrderAt_pos hf.meromorphicAt).mp (hz ▸ ht)
  · intro ho
    exact tendsto_nhds_unique ht (tendsto_zero_of_meromorphicOrderAt_pos ho)
end QEC.Coding.AlgebraicGeometry.MeromorphicGerms
