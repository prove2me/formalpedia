-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_PointGenerated_proof_66102a22e900
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:02:09.444808+00:00
-- url     : https://prove2.me/submissions/1dd79af5-1e6c-4d06-b01b-dcfc5b15de82

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GeneratedTwistSysZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PHilbertPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPointGenerated
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_PointGenerated_mem_sub_iff_6462ffb5cff7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace PointGenerated
theorem _root_.solution : PointGenerated.Statement.{u, w} := by
  intro k _ Ω _ _ N x Q hx I
  have hsecs : ∀ y, y ∈ Q.toSubSystem.secs ↔ y ∈ Q.sub I := by
    intro y
    rw [SubSystem.secs, Submodule.mem_iInf]
    exact ⟨fun h => h I, fun h J => (PointGenerated.mem_sub_iff hx Q I J y).mp h⟩
  apply le_antisymm
  · refine Submodule.span_le.mpr fun y hy => ?_
    exact (hsecs y).mp hy
  · intro y hy
    exact Submodule.subset_span ((hsecs y).mpr hy)
end PointGenerated
end GroundTheory.Heights₂.Heights.Kleiman
