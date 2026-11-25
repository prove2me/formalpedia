-- Prove2me | solution 1 for PI.FJMX.deriv_det_eq_zero_rows
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:54:21.505898+00:00
-- url     : https://prove2.me/submissions/6a9ff48f-f9ff-4d30-9827-264bbf90c95f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Theorems.Thm_PI_FJMX_deriv_det_eq_zero

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
theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n] (D : Derivation R A A)
    (M : Matrix n n A)
    (h : ∀ i, (∀ k, D (M i k) = 0) ∨ ∃ i', i' ≠ i ∧ ∃ c : A, ∀ k, D (M i k) = c * M i' k) :
    D M.det = 0 := by
  rw [← Matrix.det_transpose]
  exact deriv_det_eq_zero D M.transpose h
end PI.FJMX
