-- Prove2me | solution 1 for ZetaZeros.D.EllReg.internal_of_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:31:32.943877+00:00
-- url     : https://prove2.me/submissions/2b186b36-d576-425c-9e9a-78266ba70118

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllReg
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Theorems.Thm_ZetaZeros_D_EllReg_internal_of_leaves

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
    (hB : BaseLevel) (hSL : SymbLower) (hW : WeightDiff) (hCB : ConvBound) (hK : KernelSmall)
    (hPF : PairingFourier) (hDE : DwExp) (hFP : FourierPair) (hPL : PairingLocal) (hWF : WeakFourier)
    (hSP : StepOfParts) : Internal :=
  internal_of_leaves hM hBu hC hL hB (hSP hSL hW hCB hK hPF hDE hFP hPL hWF hBu hC)
end ZetaZeros.D.EllReg
