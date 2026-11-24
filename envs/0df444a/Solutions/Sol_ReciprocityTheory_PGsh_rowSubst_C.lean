-- Prove2me | solution 1 for ReciprocityTheory.PGsh.rowSubst_C
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:51.859051+00:00
-- url     : https://prove2.me/submissions/13f6ebe3-de09-40fc-8779-044bd0c5195e

import Definitions.Def_ReciprocityTheory_DualLattices_FischerSmulRight
import Definitions.Def_ReciprocityTheory_DualLattices_ConstantCoeffRowSubst

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
theorem _root_.solution (g : Matrix (Fin ν) (Fin ν) ℂ) (c : ℂ) :
    rowSubst g (C c : MvPolynomial (Fin ν × ι) ℂ) = C c := by
  simp [rowSubst]
end ReciprocityTheory.PGsh
