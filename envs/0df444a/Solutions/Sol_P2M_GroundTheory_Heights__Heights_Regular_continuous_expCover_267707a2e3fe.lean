-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_continuous_expCover_267707a2e3fe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:49:43.556015+00:00
-- url     : https://prove2.me/submissions/c50134da-87e5-48cb-8d58-16b665d76f28

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
theorem _root_.solution {n : ℕ} (a : ℕ) : Continuous (expCover (n := n) a) :=
  continuous_pi fun k => by
    unfold expCover
    split_ifs
    exacts [Complex.continuous_exp.comp (continuous_apply k), continuous_apply k]
end GroundTheory.Heights₂.Heights.Regular
