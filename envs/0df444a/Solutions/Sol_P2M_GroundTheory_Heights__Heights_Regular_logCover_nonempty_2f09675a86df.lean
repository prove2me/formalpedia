-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_logCover_nonempty_2f09675a86df
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:49:38.760124+00:00
-- url     : https://prove2.me/submissions/b7b42cb1-bc77-4bd4-9f4c-2fea69b0af02

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PosSemidefOfIntQuadNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Matrix Topology Filter
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
theorem _root_.solution {n a : ℕ} (h : a ≤ n) : (logCover h).Nonempty :=
  ⟨fun k => if k.val < a then -1 else 0,
    fun i => by simp [Fin.castLE, i.isLt], fun k hk => by simp [not_lt.2 hk]⟩
end GroundTheory.Heights₂.Heights.Regular
