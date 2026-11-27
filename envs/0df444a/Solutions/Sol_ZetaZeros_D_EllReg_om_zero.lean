-- Prove2me | solution 1 for ZetaZeros.D.EllReg.om_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:34:21.559639+00:00
-- url     : https://prove2.me/submissions/3eacb259-e070-4901-bc06-21835f02b723

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_BaseLevel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
namespace ZetaZeros.D.EllReg
theorem _root_.solution {d : ℕ} (s : ℝ) (ξ : E d) : om s 0 0 ξ = (1 + ‖ξ‖ ^ 2) ^ (s / 2) := by
  simp [om]
end ZetaZeros.D.EllReg
