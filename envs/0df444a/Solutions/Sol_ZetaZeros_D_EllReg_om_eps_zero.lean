-- Prove2me | solution 1 for ZetaZeros.D.EllReg.om_eps_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:06:47.327512+00:00
-- url     : https://prove2.me/submissions/3b23964a-2d16-40ee-8d8b-da3761b95f0c

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegStep
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_BaseLevel
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_WeightedNormFinite

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
theorem _root_.solution {d : ℕ} (s M : ℝ) (ξ : E d) : om s M 0 ξ = om s 0 0 ξ := by
  unfold om
  simp
end ZetaZeros.D.EllReg
