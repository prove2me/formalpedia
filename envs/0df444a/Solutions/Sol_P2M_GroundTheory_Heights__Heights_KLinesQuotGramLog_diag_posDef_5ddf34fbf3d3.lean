-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KLinesQuotGramLog_diag_posDef_5ddf34fbf3d3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:01:14.752121+00:00
-- url     : https://prove2.me/submissions/2661a089-7880-4c45-8a11-61c8bea5c716

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesQuotGramLog

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
open Matrix
open scoped ComplexOrder
open GroundTheory.Heights₂.Heights.KLinesQuotGramLog
namespace GroundTheory.Heights₂.Heights.KLinesQuotGramLog
theorem _root_.solution {n : ℕ} (d : Fin n → ℝ) (hd : ∀ x, 0 < d x) :
    (Matrix.diagonal fun x => (d x : ℂ)).PosDef :=
  PosDef.diagonal fun x => Complex.zero_lt_real.mpr (hd x)
end GroundTheory.Heights₂.Heights.KLinesQuotGramLog
