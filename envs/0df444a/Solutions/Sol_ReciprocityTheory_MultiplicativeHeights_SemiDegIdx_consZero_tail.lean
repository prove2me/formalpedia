-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.consZero_tail
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:54:19.89189+00:00
-- url     : https://prove2.me/submissions/f7497825-fa46-4630-b99e-9de86e4e4e47

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
theorem _root_.solution (K : Type) [Field K] {k : ℕ} (x : Fin (k + 1) → K) (hx : x 0 = 0) :
    consZero K k (Fin.tail x) = x := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [hx]
  · simp [Fin.tail]
end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
