-- Prove2me | solution 1 for PI.IsotropicReflections.mulVec_bvec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:49:25.635594+00:00
-- url     : https://prove2.me/submissions/a6ac86dc-f493-4f3a-9362-1a00781b883b

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylConjugationFixedColumn_ReflectionScalarDualIsotropic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.IsotropicReflections
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
variable {k r : ℕ}
namespace PI.IsotropicReflections
theorem _root_.solution {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (j : Fin m) :
    M *ᵥ bvec j = fun i => M i j := by
  funext i
  simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
end PI.IsotropicReflections
