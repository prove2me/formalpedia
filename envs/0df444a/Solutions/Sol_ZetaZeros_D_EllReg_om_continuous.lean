-- Prove2me | solution 1 for ZetaZeros.D.EllReg.om_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:06:43.966866+00:00
-- url     : https://prove2.me/submissions/d935bb4f-b006-451e-bab0-3f044137a0ee

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
theorem _root_.solution {d : ℕ} (s M ε : ℝ) : Continuous fun ξ : E d => om s M ε ξ := by
  unfold om
  exact ((continuous_const.add (continuous_norm.pow 2)).rpow_const
      fun ξ => Or.inl (add_pos_of_pos_of_nonneg one_pos (sq_nonneg _)).ne').mul
    ((continuous_const.add (continuous_const.mul (continuous_norm.pow 2))).rpow_const
      fun ξ => Or.inl (add_pos_of_pos_of_nonneg one_pos (mul_nonneg (sq_nonneg _) (sq_nonneg _))).ne')
end ZetaZeros.D.EllReg
