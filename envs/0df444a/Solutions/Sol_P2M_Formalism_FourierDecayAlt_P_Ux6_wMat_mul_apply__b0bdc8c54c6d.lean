-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_Ux6_wMat_mul_apply__b0bdc8c54c6d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:38:04.037288+00:00
-- url     : https://prove2.me/submissions/b5b289b0-ec16-46a2-b647-b37fbde9de23

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux6
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux6
theorem _root_.solution {n : ℕ} (M : Matrix (Fin j) (Fin n) ℂ) (a : Fin j) (b : Fin n) :
    (G.wMat j * M) a b = M a.rev b := by
  simp [G.wMat, Matrix.mul_apply]
end Formalism.FourierDecayAlt.P.Ux6
