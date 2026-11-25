-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.inSub_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:20:26.645812+00:00
-- url     : https://prove2.me/submissions/857b5999-205d-45dc-80c4-67bc5b6a5d88

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorSub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_inSub_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_inSub_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)
variable {C : Type} [Field C] (K : Subfield C) (W : WeierstrassCurve C)
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (hW : CoeffSub K W) (n : ℕ) (P : W.toAffine.Point) (hP : InSub K P) :
    InSub K (n • P) := by
  induction n with
  | zero => rw [zero_smul]; exact inSub_zero K W
  | succ n ih => rw [succ_nsmul]; exact inSub_add K W hW _ _ ih hP
end ReciprocityTheory.ChartRestriction.L1
