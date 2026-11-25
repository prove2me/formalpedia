-- Prove2me | solution 1 for ReciprocityTheory.PGsh.fischer_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:45:30.747056+00:00
-- url     : https://prove2.me/submissions/ccbe360f-8a04-42d3-a2c5-0c48ae76a923

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
import Definitions.Def_ReciprocityTheory_DualLattices_FischerSmulRight
import Theorems.Thm_ReciprocityTheory_PGsh_fischer_eq_sum
import Theorems.Thm_ReciprocityTheory_PGsh_fischer_add_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open scoped Classical
open ReciprocityTheory ReciprocityTheory.PGsh
variable {ν : ℕ} {ι : Type*}
namespace ReciprocityTheory.PGsh
theorem _root_.solution {α : Type*} (s : Finset α) (f : α → MvPolynomial (Fin ν × ι) ℂ)
    (Q : MvPolynomial (Fin ν × ι) ℂ) :
    fischer (∑ i ∈ s, f i) Q = ∑ i ∈ s, fischer (f i) Q := by
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    rw [fischer_eq_sum 0 Q ∅ (by simp)]
    simp
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, fischer_add_left, ih]
end ReciprocityTheory.PGsh
