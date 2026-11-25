-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GoodPointBranch_consZero_injective_e1881b5a7862
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:30:41.584095+00:00
-- url     : https://prove2.me/submissions/002d3e19-47fc-4499-868c-3aed8345f343

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
theorem _root_.solution {d : ℕ} : Function.Injective (consZero d) := fun a b h => by
  rw [consZero_apply, consZero_apply] at h
  exact Fin.cons_right_injective _ h
end GroundTheory.Heights₂.Heights.GoodPointBranch
