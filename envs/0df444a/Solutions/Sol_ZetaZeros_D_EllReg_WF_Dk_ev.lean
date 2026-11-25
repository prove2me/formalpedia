-- Prove2me | solution 1 for ZetaZeros.D.EllReg.WF.Dk_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:02:23.447157+00:00
-- url     : https://prove2.me/submissions/a56bdc0e-1308-4b2d-bfc3-a4c5b88d4591

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_WeakFourier
import Theorems.Thm_ZetaZeros_D_EllReg_WF_dw_cons
import Theorems.Thm_ZetaZeros_D_EllReg_WF_contDiff_dw
import Theorems.Thm_ZetaZeros_D_EllReg_WF_Dk_add
import Theorems.Thm_ZetaZeros_D_EllReg_WF_Dk_mul
import Theorems.Thm_ZetaZeros_D_EllReg_WF_contDiff_ev
import Theorems.Thm_ZetaZeros_D_EllReg_WF_ev_cons

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
theorem _root_.solution {L : List (List (Fin d) × (E d → ℂ))} (hL : ∀ p ∈ L, ContDiff ℝ ∞ p.2)
    {g : E d → ℂ} (hg : ContDiff ℝ ∞ g) (k : Fin d) (y : E d) :
    Dk k (ev L g) y = ev (L.map fun p => (p.1, Dk k p.2)) g y + ev (L.map fun p => (k :: p.1, p.2)) g y := by
  revert hL
  induction L with
  | nil =>
    intro _
    have h0 : ev ([] : List (List (Fin d) × (ZetaZeros.D.EllReg.E d → ℂ))) g = fun _ => 0 := by
      funext z; simp only [ev, List.map_nil, List.sum_nil]
    rw [h0]
    simp [Dk, ev]
  | cons p L ih =>
    intro hL
    have hp : ContDiff ℝ ∞ p.2 := hL p (by simp)
    have hL' : ∀ q ∈ L, ContDiff ℝ ∞ q.2 := fun q hq => hL q (by simp [hq])
    have h1 : ev (p :: L) g = fun z => p.2 z * ZetaZeros.D.EllReg.dw p.1 g z + ev L g z := by
      funext z; exact ev_cons p L g z
    rw [h1, Dk_add (hp.mul (contDiff_dw hg p.1)) (contDiff_ev hL' hg) k y,
      Dk_mul hp (contDiff_dw hg p.1) k y, ih hL']
    simp only [List.map_cons, ev_cons, dw_cons]
    ring
end ZetaZeros.D.EllReg.WF
