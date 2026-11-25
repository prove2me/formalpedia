-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.Ib.norm_chr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:52:12.542902+00:00
-- url     : https://prove2.me/submissions/04c29fa5-0742-40c8-9f02-a30584d25fa1

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_IntegrableOfBound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Ib_lf_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Ib_chr_eq

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
theorem _root_.solution (t : ℝ) (β y : E n) : ‖chr t β y‖ = 1 := by
  rw [chr_eq, Complex.norm_exp, lf_apply]
  have h : (∑ a, ∑ b, (β a b : ℂ) * (y a b : ℂ)) = ((∑ a, ∑ b, β a b * y a b : ℝ) : ℂ) := by push_cast; rfl
  rw [h]
  simp [Complex.mul_re, Complex.I_re, Complex.I_im]
end PositivityTheory.Rg.Sw.WR.Ib
