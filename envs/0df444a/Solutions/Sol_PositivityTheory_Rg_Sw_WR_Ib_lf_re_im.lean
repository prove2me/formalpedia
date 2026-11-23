-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.Ib.lf_re_im
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:54:53.956375+00:00
-- url     : https://prove2.me/submissions/177d6dcb-9a06-44bf-a3a9-15ec50aade08

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_IntegrableOfBound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Ib_lf_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Ib
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.Ib
theorem _root_.solution (t : ℝ) (β : E n) (w : Fin n → Fin n → ℂ) :
    lf t β (fun a b => (w a b).re) + Complex.I * lf t β (fun a b => (w a b).im) =
      -(Complex.I * t * ∑ a, ∑ b, (β a b : ℂ) * w a b) := by
  rw [lf_apply, lf_apply]
  have h : ∀ a b, (β a b : ℂ) * w a b =
      (β a b : ℂ) * ((w a b).re : ℂ) + Complex.I * ((β a b : ℂ) * ((w a b).im : ℂ)) := by
    intro a b
    conv_lhs => rw [← Complex.re_add_im (w a b)]
    ring
  simp_rw [h, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring
end PositivityTheory.Rg.Sw.WR.Ib
