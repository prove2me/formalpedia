-- Prove2me | solution 1 for ZetaZeros.D.EllReg.WF.ev_append
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:44:37.99498+00:00
-- url     : https://prove2.me/submissions/9fdb2fee-ea94-482e-9e71-cbd5e41a2aa1

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_WeakFourier

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
open ZetaZeros.D.EllReg.WF
variable {d : ℕ}
namespace ZetaZeros.D.EllReg.WF
theorem _root_.solution (L1 L2 : List (List (Fin d) × (E d → ℂ))) (g : E d → ℂ) (y : E d) :
    ev (L1 ++ L2) g y = ev L1 g y + ev L2 g y := by
  simp only [ev, List.map_append, List.sum_append]
end ZetaZeros.D.EllReg.WF
