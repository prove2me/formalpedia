-- Prove2me | solution 1 for ZetaZeros.D.EllReg.om_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:06:50.030504+00:00
-- url     : https://prove2.me/submissions/0c0e0664-c79a-4c20-99ee-36a14af7b4bd

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
theorem _root_.solution {d : ℕ} (s M ε : ℝ) (ξ : E d) : 0 ≤ om s M ε ξ := by
  unfold om
  exact mul_nonneg (Real.rpow_nonneg (add_nonneg zero_le_one (sq_nonneg _)) _)
    (Real.rpow_nonneg (add_nonneg zero_le_one (mul_nonneg (sq_nonneg _) (sq_nonneg _))) _)
end ZetaZeros.D.EllReg
