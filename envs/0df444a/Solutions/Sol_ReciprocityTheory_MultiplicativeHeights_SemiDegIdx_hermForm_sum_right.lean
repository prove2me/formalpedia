-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.hermForm_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:54:41.378136+00:00
-- url     : https://prove2.me/submissions/c1764b81-db86-458a-a988-697cd3cf9603

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCE
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegC
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_consZero_succ
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_consZero_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.consZero_succ
attribute [local simp] ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.consZero_zero



set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
open NumberField Matrix
open scoped nonZeroDivisors
namespace ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    {ι : Type} (s : Finset ι) (u : Fin r → K) (w : ι → Fin r → K) :
    S.h u (∑ i ∈ s, w i) = ∑ i ∈ s, S.h u (w i) := by
  classical
  refine Finset.induction_on s (by simp [HermForm.h]) ?_
  intro i s hi ih
  rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
  simp only [HermForm.h, Pi.add_apply, mul_add, Finset.sum_add_distrib]
end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
