-- Prove2me | solution 1 for ZetaZeros.D.EllReg.WF.ev_sb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:47:06.815682+00:00
-- url     : https://prove2.me/submissions/b9be655c-bf16-4f1b-a13d-68689e020a4a

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_WeakFourier
import Theorems.Thm_ZetaZeros_D_EllReg_WF_ev_cons
import Theorems.Thm_ZetaZeros_D_EllReg_WF_ev_append
import Theorems.Thm_ZetaZeros_D_EllReg_WF_ev_sc
import Theorems.Thm_ZetaZeros_D_EllReg_WF_leib

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
theorem _root_.solution {a : E d → ℂ} (ha : ContDiff ℝ ∞ a) {e : E d → ℂ} (he : ContDiff ℝ ∞ e) (y : E d) :
    ∀ L : List (List (Fin d) × (E d → ℂ)), ev L (fun z => a z * e z) y = ev (sb a L) e y
  | [] => by simp [ev, sb]
  | p :: L => by
    rw [ev_cons, solution ha he y L, leib ha p.1 e he]
    simp only [sb, ev_cons, ev_append, ev_sc]
    ring
end ZetaZeros.D.EllReg.WF
