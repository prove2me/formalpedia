-- Prove2me | solution 1 for PermanentRollout.criticalGradientIdeal_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/5ca3dc2e-d7e0-4e24-b6b1-016eca917c44

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution {m d : ℕ}
    (P : MvPolynomial (Fin m) ℂ) (hP : P.IsHomogeneous d) :
    (homogeneousMapIdeal
      (fun i : Fin m => MvPolynomial.pderiv i P)).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin m) ℂ) := by
  change
    (Ideal.span
      (Set.range fun i : Fin m => MvPolynomial.pderiv i P)).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin m) ℂ)
  apply Ideal.homogeneous_span
  rintro _ ⟨i, rfl⟩
  exact ⟨d - 1, hP.pderiv (i := i)⟩
end PermanentRollout
