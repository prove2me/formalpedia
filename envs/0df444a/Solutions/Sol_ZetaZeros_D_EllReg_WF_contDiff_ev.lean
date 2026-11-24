-- Prove2me | solution 1 for ZetaZeros.D.EllReg.WF.contDiff_ev
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:53:03.290188+00:00
-- url     : https://prove2.me/submissions/de23f9d3-3687-47e5-98b5-66ddfcd51220

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_WeakFourier
import Theorems.Thm_ZetaZeros_D_EllReg_WF_contDiff_dw

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
    {g : E d → ℂ} (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (ev L g) := by
  revert hL
  induction L with
  | nil =>
    intro _
    have h0 : ev ([] : List (List (Fin d) × (ZetaZeros.D.EllReg.E d → ℂ))) g = fun _ => 0 := by
      funext y; simp only [ev, List.map_nil, List.sum_nil]
    rw [h0]; exact contDiff_const
  | cons p L ih =>
    intro hL
    have h1 : ev (p :: L) g = fun y => p.2 y * ZetaZeros.D.EllReg.dw p.1 g y + ev L g y := by
      funext y; simp only [ev, List.map_cons, List.sum_cons]
    rw [h1]
    exact ((hL p (by simp)).mul (contDiff_dw hg p.1)).add (ih fun q hq => hL q (by simp [hq]))
end ZetaZeros.D.EllReg.WF
