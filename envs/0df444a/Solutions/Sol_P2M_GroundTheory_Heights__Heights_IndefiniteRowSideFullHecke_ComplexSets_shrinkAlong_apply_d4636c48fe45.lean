-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_shrinkAlong_apply_d4636c48fe45
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:32.402285+00:00
-- url     : https://prove2.me/submissions/b4237eab-725d-4806-86f2-a10d85fe9da9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCriticalImageNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCriticalImageNull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution (i0 : ι) (k : ι → ℝ) (δ : ℝ) (z : ι → ℝ) :
    shrinkAlong i0 k δ z = z - ((1 - δ) * z i0) • k := by
  simp [shrinkAlong, smul_smul]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
