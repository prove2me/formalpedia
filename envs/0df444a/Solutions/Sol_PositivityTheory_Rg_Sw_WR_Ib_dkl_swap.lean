-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.Ib.dkl_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:10:59.812573+00:00
-- url     : https://prove2.me/submissions/6418e3b8-9363-4721-9c3d-b7ed334bd469

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_IntegrableOfBound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Ib_vkl_swap

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
theorem _root_.solution (g : E n → ℂ) (k l : Fin n) (y : E n) :
    Dkl l k g y = fderiv ℝ g y (fun a b => (vkl k l a b).re) -
      Complex.I * fderiv ℝ g y (fun a b => (vkl k l a b).im) := by
  have e1 : (fun a b => (vkl l k a b).re) = fun a b => (vkl k l a b).re := by
    funext a b; rw [vkl_swap]; simp
  have e2 : (fun a b => (vkl l k a b).im) = -(fun a b => (vkl k l a b).im) := by
    funext a b; rw [vkl_swap]; simp
  simp only [Dkl, dirC]
  rw [e1, e2, map_neg]
  ring
end PositivityTheory.Rg.Sw.WR.Ib
