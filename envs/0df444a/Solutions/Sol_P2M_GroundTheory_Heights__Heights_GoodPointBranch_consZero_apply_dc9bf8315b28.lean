-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GoodPointBranch_consZero_apply_dc9bf8315b28
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:37.648537+00:00
-- url     : https://prove2.me/submissions/f67d15f7-9851-4ebf-a40e-11a07f679fa4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorGoodPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_NormalModelFibreNear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GoodPointBranchSlice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Filter Topology Matrix ComplexSets Metric Set
noncomputable section
open GroundTheory.Heights₂.Heights.GoodPointBranch
namespace GroundTheory.Heights₂.Heights.GoodPointBranch
theorem _root_.solution {d : ℕ} (v : Fin d → ℂ) : consZero d v = Fin.cons 0 v := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [consZero]
end GroundTheory.Heights₂.Heights.GoodPointBranch
