-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.T.norm_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:54:10.154465+00:00
-- url     : https://prove2.me/submissions/99f48993-91a7-473a-91a7-db570d728327

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DifferentiableOfTop
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousHerm
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_T_norm_chr
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_T_dP_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.T
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.T
theorem _root_.solution (hI : Integr) (t : ℝ) (β : E n) (h : E n → ℂ) (z : ℂ) (y : E n) :
    ‖((dP y : ℝ) : ℂ) ^ (-z) * h y * chr t β y‖ = dP y ^ (-z.re) * ‖h y‖ := by
  rw [norm_mul, norm_mul, norm_chr, mul_one, Complex.norm_cpow_eq_rpow_re_of_pos (dP_pos hI y), Complex.neg_re]
end PositivityTheory.Rg.Sw.WR.T
