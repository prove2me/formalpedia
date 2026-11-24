-- Prove2me | solution 1 for ReciprocityTheory.PGsh.fischer_add_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:51.604994+00:00
-- url     : https://prove2.me/submissions/96963bf7-cb60-4f01-ab78-f0b29f7473b5

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
theorem _root_.solution (P Q Q' : MvPolynomial (Fin ν × ι) ℂ) :
    fischer P (Q + Q') = fischer P Q + fischer P Q' := by
  rw [fischer_eq_sum P (Q + Q') P.support (Finset.Subset.refl _),
    fischer_eq_sum P Q P.support (Finset.Subset.refl _),
    fischer_eq_sum P Q' P.support (Finset.Subset.refl _), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [MvPolynomial.coeff_add, map_add]
  ring
end ReciprocityTheory.PGsh
