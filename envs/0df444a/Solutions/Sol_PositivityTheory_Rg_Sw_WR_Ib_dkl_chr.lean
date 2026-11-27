-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.Ib.dkl_chr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:20:46.320256+00:00
-- url     : https://prove2.me/submissions/494ed05d-c690-414c-98ac-219060ce8fed

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_IntegrableOfBound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Ib_fderiv_chr
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Ib_lf_re_im
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Ib_sum_vkl

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
theorem _root_.solution (t : ℝ) (β : E n) (k l : Fin n) (y : E n) :
    Dkl k l (chr t β) y = (-(Complex.I * t) * herm β k l) * chr t β y := by
  have h := lf_re_im t β (vkl k l)
  rw [sum_vkl] at h
  simp only [Dkl, dirC, fderiv_chr]
  linear_combination (chr t β y) * h
end PositivityTheory.Rg.Sw.WR.Ib
