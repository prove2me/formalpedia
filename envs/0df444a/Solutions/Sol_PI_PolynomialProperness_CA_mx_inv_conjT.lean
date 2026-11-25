-- Prove2me | solution 1 for PI.PolynomialProperness.CA.mx_inv_conjT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:04:00.92198+00:00
-- url     : https://prove2.me/submissions/74b58db6-e841-469d-a0a2-c288593d04fb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_NsqMulVecLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInverseBoundOf
import Theorems.Thm_PI_PolynomialProperness_GN_mx_conjTranspose


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
open scoped ComplexConjugate
noncomputable section
open PI PI.PolynomialProperness PI.PolynomialProperness.CA
namespace PI.PolynomialProperness.CA
theorem _root_.solution {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) : mx (Mᴴ)⁻¹ = mx M⁻¹ := by
  rw [← conjTranspose_nonsing_inv, GN.mx_conjTranspose]
end PI.PolynomialProperness.CA
