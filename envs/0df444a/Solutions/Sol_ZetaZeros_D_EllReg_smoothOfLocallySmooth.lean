-- Prove2me | solution 1 for ZetaZeros.D.EllReg.smoothOfLocallySmooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:10:15.262025+00:00
-- url     : https://prove2.me/submissions/a2caa5c7-9229-44ac-83bf-b0140bf32c55

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
theorem _root_.solution : LocalGlobal := by
  intro d U f _ h x hx
  obtain ⟨χ, hχ1, hχf⟩ := h x hx
  have heq : cut χ f =ᶠ[𝓝 x] f := by
    filter_upwards [hχ1] with y hy
    simp [cut, hy]
  exact (hχf.contDiffAt.congr_of_eventuallyEq heq.symm).contDiffWithinAt
end ZetaZeros.D.EllReg
