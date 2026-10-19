-- Prove2me | solution 1 for PermanentRollout.gradientVector_smul_of_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/dee7e608-90b8-4dbd-9e39-ae8874f5c452

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneous_eval_smul

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization
namespace PermanentRollout
theorem _root_.solution {m d : ℕ}
    (P : MvPolynomial (Fin m) ℂ) (hP : P.IsHomogeneous d)
    (a : ℂ) (v : Fin m → ℂ) :
    gradientVector P (a • v) = a ^ (d - 1) • gradientVector P v := by
  funext i
  simpa [gradientVector] using
    homogeneous_eval_smul (MvPolynomial.pderiv i P) (hP.pderiv (i := i)) a v
end PermanentRollout
