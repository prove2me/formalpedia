-- Prove2me | solution 1 for ZetaZeros.D.EllReg.Dec.tsupport_cut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:00:26.45895+00:00
-- url     : https://prove2.me/submissions/6ac2d54f-30a2-419e-be90-5771fffb31cb

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegStep
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_Decompose

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
open ZetaZeros.D.EllReg.Dec
variable {d : ℕ}
namespace ZetaZeros.D.EllReg.Dec
theorem _root_.solution (χ : E d → ℝ) (u : E d → ℂ) : tsupport (cut χ u) ⊆ tsupport χ := by
  exact (tsupport_mul_subset_left).trans (tsupport_comp_subset Complex.ofReal_zero χ)
end ZetaZeros.D.EllReg.Dec
