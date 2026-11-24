-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBound_LimitInEpsilon_proof_3338cae8e7d1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:49:24.884727+00:00
-- url     : https://prove2.me/submissions/07cfbbfc-7520-47cf-8dd2-27ada94a1c5c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_PLimitInEpsilon

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBound
open Real Filter Topology
namespace GroundTheory.Heights₂.Heights.LowerBound
namespace LimitInEpsilon
theorem _root_.solution : LimitInEpsilon.Statement := by
  intro n P Q W W0 e' C1 H
  obtain ⟨hP, hQ, hW, hb⟩ := H
  have hε : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hP' : Tendsto P (𝓝[>] 0) (𝓝 (P 0)) := hP
  have hQ' : Tendsto Q (𝓝[>] 0) (𝓝 (Q 0)) := hQ
  have hL : Tendsto (fun ε => (n + 1 : ℝ) * ((e' - ε * C1) * Q ε - 1 / 2 * W ε))
      (𝓝[>] 0) (𝓝 ((n + 1 : ℝ) * ((e' - 0 * C1) * Q 0 - 1 / 2 * W0))) :=
    tendsto_const_nhds.mul
      (((tendsto_const_nhds.sub (hε.mul tendsto_const_nhds)).mul hQ').sub
        (tendsto_const_nhds.mul hW))
  have key : (n + 1 : ℝ) * ((e' - 0 * C1) * Q 0 - 1 / 2 * W0) ≤ P 0 :=
    le_of_tendsto_of_tendsto hL hP' hb
  have e : (n + 1 : ℝ) * ((e' - 0 * C1) * Q 0 - 1 / 2 * W0) =
      (n + 1) * (e' * Q 0 - W0 / 2) := by ring
  rw [e] at key
  exact key
end LimitInEpsilon
end GroundTheory.Heights₂.Heights.LowerBound
