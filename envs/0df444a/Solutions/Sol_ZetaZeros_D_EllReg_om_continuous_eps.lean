-- Prove2me | solution 1 for ZetaZeros.D.EllReg.om_continuous_eps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:06:45.168285+00:00
-- url     : https://prove2.me/submissions/e8c337a4-0365-4358-8034-557c861196bd

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
theorem _root_.solution {d : ℕ} (s M : ℝ) (ξ : E d) : Continuous fun ε : ℝ => om s M ε ξ := by
  unfold om
  exact continuous_const.mul
    ((continuous_const.add ((continuous_pow 2).mul continuous_const)).rpow_const
      fun ε => Or.inl (add_pos_of_pos_of_nonneg one_pos (mul_nonneg (sq_nonneg _) (sq_nonneg _))).ne')
end ZetaZeros.D.EllReg
