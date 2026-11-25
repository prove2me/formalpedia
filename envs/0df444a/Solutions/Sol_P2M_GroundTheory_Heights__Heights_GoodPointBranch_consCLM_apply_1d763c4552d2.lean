-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GoodPointBranch_consCLM_apply_1d763c4552d2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:30:38.997242+00:00
-- url     : https://prove2.me/submissions/a16f038c-652c-4be8-b315-30f1a4f21a16

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
theorem _root_.solution {d : ℕ} (p : ℂ × (Fin d → ℂ)) : consCLM d p = vecCons p.1 p.2 := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [consCLM]
end GroundTheory.Heights₂.Heights.GoodPointBranch
