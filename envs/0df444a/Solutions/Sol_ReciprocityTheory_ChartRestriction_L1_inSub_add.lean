-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.inSub_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:05:25.91661+00:00
-- url     : https://prove2.me/submissions/0f9c5fd5-0f03-449b-a582-f63214f80855

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorSub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_slope_mem_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_addX_mem_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_addY_mem_sub

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
theorem _root_.solution (hW : CoeffSub K W) (P Q : W.toAffine.Point) (hP : InSub K P) (hQ : InSub K Q) :
    InSub K (P + Q) := by
  cases P with
  | zero =>
    change InSub K ((0 : W.toAffine.Point) + _)
    rwa [zero_add]
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero =>
      change InSub K (_ + (0 : W.toAffine.Point))
      rwa [add_zero]
    | some x₂ y₂ h₂ =>
      by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
      · rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hxy.1 hxy.2]
        trivial
      · rw [WeierstrassCurve.Affine.Point.add_some hxy]
        have hs := slope_mem_sub K W hW hP.1 hQ.1 hP.2 hQ.2
        exact ⟨addX_mem_sub K W hW hP.1 hQ.1 hs, addY_mem_sub K W hW hP.1 hQ.1 hP.2 hs⟩
end ReciprocityTheory.ChartRestriction.L1
