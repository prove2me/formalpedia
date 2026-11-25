-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.inSub_px
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:49:22.246324+00:00
-- url     : https://prove2.me/submissions/ae07c1e1-a022-4bd2-81ff-d0dc5db95aa7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorSub

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
theorem _root_.solution (P : W.toAffine.Point) (hP : InSub K P) : px W P ∈ K ∧ py W P ∈ K := by
  cases P with
  | zero => exact ⟨K.zero_mem, K.zero_mem⟩
  | some x y h => exact hP
end ReciprocityTheory.ChartRestriction.L1
