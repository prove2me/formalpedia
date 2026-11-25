-- Prove2me | solution 1 for ZetaZeros.D.EllReg.integralFourierChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:07:44.9528+00:00
-- url     : https://prove2.me/submissions/6630ab67-305c-4824-9a10-e241825f79b1

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_SmoothOfLocallySmooth

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
theorem _root_.solution : FourierPair := by
  intro d g _ _ ξ
  rw [Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show g y * eF ξ y = Complex.exp (((-2 * Real.pi * inner ℝ y ξ : ℝ) : ℂ) * Complex.I) • g y
  rw [smul_eq_mul, mul_comm (Complex.exp _)]
  congr 1
  simp only [eF]
  congr 1
  push_cast
  ring
end ZetaZeros.D.EllReg
