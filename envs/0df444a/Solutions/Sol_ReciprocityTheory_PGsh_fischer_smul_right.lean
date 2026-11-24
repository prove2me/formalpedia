-- Prove2me | solution 1 for ReciprocityTheory.PGsh.fischer_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:51.74787+00:00
-- url     : https://prove2.me/submissions/4d844e2e-6a51-4572-af4f-0077b039d212

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
    fischer P (c • Q) = starRingEnd ℂ c * fischer P Q := by
  rw [fischer_eq_sum P (c • Q) P.support (Finset.Subset.refl _),
    fischer_eq_sum P Q P.support (Finset.Subset.refl _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, map_mul]
  ring
end ReciprocityTheory.PGsh
