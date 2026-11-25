-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.slope_mem_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:40:43.089881+00:00
-- url     : https://prove2.me/submissions/dab88f34-3e3a-4ba3-9f50-23c82fec7ce8

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
theorem _root_.solution (hW : CoeffSub K W) {x₁ x₂ y₁ y₂ : C} (hx₁ : x₁ ∈ K) (hx₂ : x₂ ∈ K)
    (hy₁ : y₁ ∈ K) (hy₂ : y₂ ∈ K) : W.toAffine.slope x₁ x₂ y₁ y₂ ∈ K := by
  have n1 := negY_mem_sub K W hW hx₁ hy₁
  have n2 := negY_mem_sub K W hW hx₂ hy₂
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  have c2 : (2 : C) ∈ K := by
    have h0 := natCast_mem K 2
    simpa using h0
  have c3 : (3 : C) ∈ K := by
    have h0 := natCast_mem K 3
    simpa using h0
  unfold WeierstrassCurve.Affine.slope
  split_ifs
  · exact K.zero_mem
  · repeat (first
    | assumption
    | exact K.zero_mem
    | exact K.one_mem
    | apply K.div_mem
    | apply K.sub_mem
    | apply K.add_mem
    | apply K.mul_mem
    | apply K.pow_mem
    | apply K.neg_mem)
  · repeat (first
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
