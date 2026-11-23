-- Prove2me | solution 1 for ZetaZeros.D.EllReg.derivL1Norm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:42:52.252794+00:00
-- url     : https://prove2.me/submissions/9c8c1105-f4de-4d6c-95d3-b36df1f79f9e

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernDecay

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
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace ZetaZeros.D.EllReg
theorem _root_.solution (f : V → ℂ) (n : ℕ) : 0 ≤ derivL1Norm f n :=
  Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => norm_nonneg _
end ZetaZeros.D.EllReg
