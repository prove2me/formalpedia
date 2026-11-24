-- Prove2me | solution 1 for PositivityTheory.KReal.low_rai
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:47.823475+00:00
-- url     : https://prove2.me/submissions/ec7e94bf-457d-44fd-b94f-138c3eabdf8e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_JointShape
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_FockAct1FockAct2Commute
import Theorems.Thm_PositivityTheory_KReal_pd_pd
import Theorems.Thm_PositivityTheory_KReal_mx_mx
import Theorems.Thm_PositivityTheory_KReal_pd_mx

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial FockH1Action
open PositivityTheory PositivityTheory.KReal
variable {p q r s : ℕ}
namespace PositivityTheory.KReal
theorem _root_.solution (a b : Ln p q r s) :
    lowB a * raiB b = raiB b * lowB a + if a = b then 1 else 0 := by
  unfold lowB raiB
  by_cases ha : linePos a = true <;> by_cases hb : linePos b = true
  · rw [if_pos ha, if_pos hb, pd_mx]
  · have hne : a ≠ b := fun h => hb (h ▸ ha)
    rw [if_pos ha, if_neg hb, mul_neg, neg_mul, pd_pd, if_neg hne, add_zero]
  · have hne : a ≠ b := fun h => ha (h ▸ hb)
    rw [if_neg ha, if_pos hb, mx_mx, if_neg hne, add_zero]
  · rw [if_neg ha, if_neg hb, mul_neg, neg_mul, pd_mx]
    by_cases h : a = b
    · rw [if_pos h, if_pos h.symm]; abel
    · rw [if_neg h, if_neg (Ne.symm h)]; abel
end PositivityTheory.KReal
