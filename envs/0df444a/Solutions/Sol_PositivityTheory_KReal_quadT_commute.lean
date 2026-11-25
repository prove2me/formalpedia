-- Prove2me | solution 1 for PositivityTheory.KReal.quadT_commute
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:30:55.232057+00:00
-- url     : https://prove2.me/submissions/cd3b58e3-c0ef-41a8-b7de-adf4a25d7acf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_JointShape
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_FockAct1FockAct2Commute
import Theorems.Thm_PositivityTheory_KReal_quartT_comm
import Theorems.Thm_PositivityTheory_KReal_quadT_mul

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
variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Ring E] [Algebra ℂ E]
namespace PositivityTheory.KReal
theorem _root_.solution (R L : ι → E) (hR : ∀ a b, R a * R b = R b * R a)
    (hL : ∀ a b, L a * L b = L b * L a)
    (hLR : ∀ a b, L a * R b = R b * L a + if a = b then 1 else 0) (A B : Matrix ι ι ℂ)
    (h : A * B = B * A) : quadT R L A * quadT R L B = quadT R L B * quadT R L A := by
  rw [quadT_mul R L hLR, quadT_mul R L hLR, h, quartT_comm R L hR hL]
end PositivityTheory.KReal
