-- Prove2me | solution 1 for ReciprocityTheory.PGsh.fischer_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:59.848479+00:00
-- url     : https://prove2.me/submissions/c74b314d-543e-442a-86cc-afbd477a019c

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
import Definitions.Def_ReciprocityTheory_DualLattices_FischerSmulRight
import Theorems.Thm_ReciprocityTheory_PGsh_fischer_eq_sum
import Theorems.Thm_ReciprocityTheory_PGsh_fischer_add_right

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
theorem _root_.solution {α : Type*} (s : Finset α) (P : MvPolynomial (Fin ν × ι) ℂ)
    (f : α → MvPolynomial (Fin ν × ι) ℂ) :
    fischer P (∑ i ∈ s, f i) = ∑ i ∈ s, fischer P (f i) := by
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    rw [fischer_eq_sum P 0 P.support (Finset.Subset.refl _)]
    simp
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, fischer_add_right, ih]
end ReciprocityTheory.PGsh
