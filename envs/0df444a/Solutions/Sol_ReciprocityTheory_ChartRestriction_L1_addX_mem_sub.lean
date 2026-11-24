-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.addX_mem_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:40:12.546645+00:00
-- url     : https://prove2.me/submissions/510e0e42-695c-4db2-9940-b98a21e89095

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
theorem _root_.solution (hW : CoeffSub K W) {x₁ x₂ s : C} (hx₁ : x₁ ∈ K) (hx₂ : x₂ ∈ K)
    (hs : s ∈ K) : W.toAffine.addX x₁ x₂ s ∈ K := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  simp only [WeierstrassCurve.Affine.addX]
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
end ReciprocityTheory.ChartRestriction.L1
