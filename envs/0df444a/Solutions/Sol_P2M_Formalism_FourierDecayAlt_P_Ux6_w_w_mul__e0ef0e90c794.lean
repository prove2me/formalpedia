-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_Ux6_w_w_mul__e0ef0e90c794
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:38:04.900797+00:00
-- url     : https://prove2.me/submissions/f021fcdd-634a-486a-bd61-10209c97d578

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_wMat_mul_self

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
theorem _root_.solution {n : ℕ} (M : Matrix (Fin j) (Fin n) ℂ) : G.wMat j * (G.wMat j * M) = M := by
  rw [← Matrix.mul_assoc, wMat_mul_self, Matrix.one_mul]
end Formalism.FourierDecayAlt.P.Ux6
