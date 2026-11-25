-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.consZero_mem_intVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:54:13.614314+00:00
-- url     : https://prove2.me/submissions/737320f0-d79f-45b4-bdf7-5d275dc01dd5

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCA
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCB
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_consZero_zero
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_consZero_succ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.consZero_zero
attribute [local simp] ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.consZero_succ

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
open NumberField
open scoped nonZeroDivisors
namespace ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
theorem _root_.solution (K : Type) [Field K] [NumberField K] {k : ℕ} {y : Fin k → K} :
    consZero K k y ∈ intVec K (k + 1) ↔ y ∈ intVec K k := by
  simp only [intVec, Submodule.mem_pi, Set.mem_univ, forall_const]
  constructor
  · intro h i
    simpa using h i.succ
  · intro h i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Submodule.zero_mem]
    · simpa using h j
end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
