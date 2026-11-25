-- Prove2me | solution 1 for ReciprocityTheory.PGsh.coeff_zero_rowSubst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:59:23.253718+00:00
-- url     : https://prove2.me/submissions/ec481f92-cfe3-4660-96cc-0a2d35999980

import Definitions.Def_ReciprocityTheory_DualLattices_FischerSmulRight
import Definitions.Def_ReciprocityTheory_DualLattices_ConstantCoeffRowSubst
import Theorems.Thm_ReciprocityTheory_PGsh_constantCoeff_rowSubst

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
theorem _root_.solution (h : Matrix (Fin ν) (Fin ν) ℂ) (Q : MvPolynomial (Fin ν × ι) ℂ) :
    coeff 0 (rowSubst h Q) = coeff 0 Q := by
  exact constantCoeff_rowSubst h Q
end ReciprocityTheory.PGsh
