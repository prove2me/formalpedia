-- Prove2me | solution 1 for ZetaZeros.D.EllReg.internal_of_leaves
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:21:03.132583+00:00
-- url     : https://prove2.me/submissions/7492a8bc-97b5-4a3f-b2da-747e85b227d2

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllReg
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Theorems.Thm_ZetaZeros_D_EllReg_localSobolev_of

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
variable {d : ℕ}
namespace ZetaZeros.D.EllReg
theorem _root_.solution (hM : MomentsSmooth) (hBu : Bump) (hC : CutCont) (hL : LocalGlobal)
    (hB : BaseLevel) (hS : Step) : Internal := by
  intro d ι _ P U u hH
  apply hL d U u hH.1
  intro x0 hx0
  obtain ⟨r, hr, hrU, hsob⟩ := localSobolev_of hB hC hS d ι P U u hH x0 hx0
  obtain ⟨χ, hχ, hχc, hχs, hχ1⟩ := hBu d x0 r hr
  refine ⟨χ, hχ1, ?_⟩
  have hcc := hC d U u χ hH.1 hH.2.2.2.1 hχ hχc (hχs.trans hrU)
  exact hM d (cut χ u) hcc.1 hcc.2 (hsob χ hχ hχc hχs)
end ZetaZeros.D.EllReg
