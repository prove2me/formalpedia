-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.addY_mem_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:33:06.968465+00:00
-- url     : https://prove2.me/submissions/ceb5b16e-2833-4618-b088-35a5b3403e60

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorSub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_negY_mem_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_addX_mem_sub

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
theorem _root_.solution (hW : CoeffSub K W) {x₁ x₂ y₁ s : C} (hx₁ : x₁ ∈ K) (hx₂ : x₂ ∈ K)
    (hy₁ : y₁ ∈ K) (hs : s ∈ K) : W.toAffine.addY x₁ x₂ y₁ s ∈ K := by
  have hX := addX_mem_sub K W hW hx₁ hx₂ hs
  have hN : W.toAffine.negAddY x₁ x₂ y₁ s ∈ K := by
    simp only [WeierstrassCurve.Affine.negAddY]
    repeat (first
    | assumption
    | exact K.zero_mem
    | exact K.one_mem
    | apply K.div_mem
    | apply K.sub_mem
    | apply K.add_mem
    | apply K.mul_mem
    | apply K.pow_mem
    | apply K.neg_mem)
  simp only [WeierstrassCurve.Affine.addY]
  exact negY_mem_sub K W hW hX hN
end ReciprocityTheory.ChartRestriction.L1
