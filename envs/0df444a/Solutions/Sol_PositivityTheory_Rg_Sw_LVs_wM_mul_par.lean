-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.wM_mul_par
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:47:25.339366+00:00
-- url     : https://prove2.me/submissions/8339e3e1-488e-4024-99e1-08e1d7b3c03c

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulConjTransposeEq
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_det_lower_right_parabolic_ne_zero
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_automorphy_first_mul_parabolic
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_automorphy_second_mul_parabolic


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
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution {P : M2 n} (hP : InP P) (x : M2 n) : wM (P * x) = wM x := by
  have hD : IsUnit P.toBlocks₂₂ := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (det_lower_right_parabolic_ne_zero hP))
  rw [wM, wM, automorphy_first_mul_parabolic x hP.2, automorphy_second_mul_parabolic x hP.2, Matrix.mul_inv_rev, Matrix.mul_assoc,
    ← Matrix.mul_assoc (P.toBlocks₂₂)⁻¹, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hD),
    Matrix.one_mul]
end PositivityTheory.Rg.Sw.LVs
