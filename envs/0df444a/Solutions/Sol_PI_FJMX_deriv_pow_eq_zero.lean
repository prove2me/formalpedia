-- Prove2me | solution 1 for PI.FJMX.deriv_pow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:24.096798+00:00
-- url     : https://prove2.me/submissions/7ac2fc87-6a3a-43e9-bcc0-b242cd33b4f4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.FJMX
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
namespace PI.FJMX
theorem _root_.solution (D : Derivation R A A) (a : A) (n : ℕ) (h : D a = 0) :
    D (a ^ n) = 0 := by
  rw [D.leibniz_pow, h]; simp
end PI.FJMX
