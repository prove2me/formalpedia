-- Prove2me | solution 1 for PermanentRollout.gradientVector_comp_linearMap_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/3040091e-e04a-4027-baf5-c7839dffe8c5

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization
namespace PermanentRollout
theorem _root_.solution {m k : ℕ}
    (P : MvPolynomial (Fin m) ℂ)
    (W : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ)) :
    ContDiff ℝ 1 (fun u : Fin k → ℂ => gradientVector P (W u)) := by
  apply contDiff_pi.mpr
  intro i
  change ContDiff ℝ 1
    (fun u : Fin k → ℂ =>
      MvPolynomial.eval (W u) (MvPolynomial.pderiv i P))
  exact (AnalyticOnNhd.eval_linearMap W
    (MvPolynomial.pderiv i P)).contDiff.restrict_scalars ℝ
end PermanentRollout
