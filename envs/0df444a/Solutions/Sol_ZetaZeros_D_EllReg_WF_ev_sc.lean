-- Prove2me | solution 1 for ZetaZeros.D.EllReg.WF.ev_sc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:31:32.894732+00:00
-- url     : https://prove2.me/submissions/70e33872-3973-4e7e-b53d-41f20743a21a

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_WeakFourier
import Theorems.Thm_ZetaZeros_D_EllReg_WF_ev_cons
import Theorems.Thm_ZetaZeros_D_EllReg_WF_ev_nil

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
theorem _root_.solution (C : E d → ℂ) (L : List (List (Fin d) × (E d → ℂ))) (g : E d → ℂ) (y : E d) :
    ev (sc C L) g y = C y * ev L g y := by
  induction L with
  | nil => simp only [sc, List.map_nil, ev_nil, mul_zero]
  | cons p L ih =>
    have h1 : sc C (p :: L) = (p.1, fun z => C z * p.2 z) :: sc C L := rfl
    rw [h1]
    simp only [ev_cons, ih]
    ring
end ZetaZeros.D.EllReg.WF
