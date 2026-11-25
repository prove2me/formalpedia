-- Prove2me | solution 1 for PositivityTheory.KReal.casW_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:57:19.665885+00:00
-- url     : https://prove2.me/submissions/511235b1-95ac-40ef-a4ab-68ddecfa5906

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasW
import Theorems.Thm_PositivityTheory_KReal_cw_blk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
namespace PositivityTheory.KReal
theorem _root_.solution {r s : ℕ} (μ : Ix r s → ℚ) : casW μ = ∑ x, μ x ^ 2 + ∑ x, rho2 x * μ x := by
  unfold casW
  congr 1
  simp only [Fintype.sum_sum_type, posC, rho2]
  simp only [if_false, ite_false, Finset.sum_const_zero, add_zero, zero_add]
  rw [cw_blk, cw_blk]
end PositivityTheory.KReal
