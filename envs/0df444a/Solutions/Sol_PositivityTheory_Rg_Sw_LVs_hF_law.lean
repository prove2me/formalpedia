-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.hF_law
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:55:48.144473+00:00
-- url     : https://prove2.me/submissions/01aaf10c-92c5-4a0a-8016-d60d4828ebd1

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulConjTransposeEq
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_wM_mul_par
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
theorem _root_.solution (j : ℕ) (p q : ℤ) {P x : M2 n} (hP : InP P) (hx : x ∈ Dom n) :
    hF j p q (P * x) = c1 p q P * hF j p q x := by
  simp only [hF, wM_mul_par hP, f0, c1, automorphy_first_mul_parabolic x hP.2, automorphy_second_mul_parabolic x hP.2, det_mul, mul_zpow]
  ring
end PositivityTheory.Rg.Sw.LVs
