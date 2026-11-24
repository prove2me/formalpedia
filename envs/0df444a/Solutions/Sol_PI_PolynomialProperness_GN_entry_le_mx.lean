-- Prove2me | solution 1 for PI.PolynomialProperness.GN.entry_le_mx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:55:44.664291+00:00
-- url     : https://prove2.me/submissions/8ca08e72-32b6-4e0d-af6d-9da4f5e21c2e

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open PI PI.PolynomialProperness PI.PolynomialProperness.GN
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt
namespace PI.PolynomialProperness.GN
theorem _root_.solution {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (i j : Fin m) : ‖M i j‖ ≤ C2.mx M := by
  unfold C2.mx
  calc ‖M i j‖ = ‖(Matrix.of.symm M) i j‖ := rfl
    _ ≤ ‖(Matrix.of.symm M) i‖ := norm_le_pi_norm _ j
    _ ≤ ‖Matrix.of.symm M‖ := norm_le_pi_norm _ i
end PI.PolynomialProperness.GN
