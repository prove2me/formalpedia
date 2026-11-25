-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.inSub_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:37:56.856972+00:00
-- url     : https://prove2.me/submissions/4c5a24af-f2fb-4f74-a8e8-8c7c5fd117fc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorSub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_negY_mem_sub

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
theorem _root_.solution (hW : CoeffSub K W) (P : W.toAffine.Point) (hP : InSub K P) : InSub K (-P) := by
  cases P with
  | zero => trivial
  | some x y h =>
    rw [WeierstrassCurve.Affine.Point.neg_some]
    exact ⟨hP.1, negY_mem_sub K W hW hP.1 hP.2⟩
end ReciprocityTheory.ChartRestriction.L1
