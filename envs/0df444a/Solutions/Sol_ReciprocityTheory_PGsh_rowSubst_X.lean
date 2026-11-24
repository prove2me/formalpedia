-- Prove2me | solution 1 for ReciprocityTheory.PGsh.rowSubst_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:34.353341+00:00
-- url     : https://prove2.me/submissions/4b4e6736-d89a-48c2-a018-bab4bf4c5f73

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
theorem _root_.solution (g : Matrix (Fin ν) (Fin ν) ℂ) (p : Fin ν × ι) :
    rowSubst g (X p) = ∑ l, C (g l p.1) * X (l, p.2) := by
  simp [rowSubst]
end ReciprocityTheory.PGsh
