-- Prove2me | solution 1 for ReciprocityTheory.PGsh.fischer_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:54.167842+00:00
-- url     : https://prove2.me/submissions/8e05cce2-9405-4262-9519-ad8ba2f8e41b

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
import Definitions.Def_ReciprocityTheory_DualLattices_FischerSmulRight
import Theorems.Thm_ReciprocityTheory_PGsh_fischer_eq_sum

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
theorem _root_.solution (c : ℂ) (P Q : MvPolynomial (Fin ν × ι) ℂ) :
    fischer (c • P) Q = c * fischer P Q := by
  have hsub : (c • P).support ⊆ P.support := by
    intro A hA
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_smul] at hA
    rw [MvPolynomial.mem_support_iff]
    intro h
    apply hA
    rw [h, smul_zero]
  rw [fischer_eq_sum (c • P) Q P.support hsub,
    fischer_eq_sum P Q P.support (Finset.Subset.refl _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  ring
end ReciprocityTheory.PGsh
