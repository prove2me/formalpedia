-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GoodPointBranch_consZero_apply_zero_f8796c3b106b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:09.395954+00:00
-- url     : https://prove2.me/submissions/2828d30d-5f3d-4960-a81c-5b1aa940948c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorGoodPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_NormalModelFibreNear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GoodPointBranchSlice
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GoodPointBranch_consZero_apply_dc9bf8315b28

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
theorem _root_.solution {d : ℕ} (v : Fin d → ℂ) : consZero d v 0 = 0 := by
  rw [consZero_apply]
  rfl
end GroundTheory.Heights₂.Heights.GoodPointBranch
