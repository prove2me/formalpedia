-- Prove2me | solution 1 for ReciprocityTheory.PGsh.pderiv_rowSubst_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:53:10.669993+00:00
-- url     : https://prove2.me/submissions/691dd550-15f4-4569-a62c-5bf0208f39c1

import Definitions.Def_ReciprocityTheory_DualLattices_FischerSmulRight
import Definitions.Def_ReciprocityTheory_DualLattices_ConstantCoeffRowSubst
import Theorems.Thm_ReciprocityTheory_PGsh_rowSubst_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Finset
open scoped Classical
open ReciprocityTheory ReciprocityTheory.PGsh
variable {ν : ℕ} {ι : Type*}
namespace ReciprocityTheory.PGsh
theorem _root_.solution (h : Matrix (Fin ν) (Fin ν) ℂ) (k : Fin ν) (a : ι) (s : Fin ν × ι) :
    pderiv (k, a) (rowSubst h (X s : MvPolynomial (Fin ν × ι) ℂ)) =
      if s.2 = a then C (h k s.1) else 0 := by
  rw [rowSubst_X, map_sum]
  by_cases hs : s.2 = a
  · simp [pderiv_C_mul, pderiv_X, Pi.single_apply, hs]
  · simp [pderiv_C_mul, pderiv_X, Pi.single_apply, hs]
end ReciprocityTheory.PGsh
