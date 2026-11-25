-- Prove2me | solution 1 for PI.IsotropicReflections.herm_bvec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:15:53.393801+00:00
-- url     : https://prove2.me/submissions/ad7151c3-66c1-4548-9dd9-3fabcc71bd8f

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
theorem _root_.solution {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ) (j : Fin m) :
    herm H v (bvec j) = (H *ᵥ v) j := by
  simp only [herm, bvec]
  rw [← Pi.single_star, star_one, single_dotProduct, one_mul]
end PI.IsotropicReflections
