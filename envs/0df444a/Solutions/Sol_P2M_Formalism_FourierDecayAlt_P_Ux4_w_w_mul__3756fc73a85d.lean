-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_Ux4_w_w_mul__3756fc73a85d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:38:01.542518+00:00
-- url     : https://prove2.me/submissions/2027cb10-33cb-4aa6-a68e-34a334af0050

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_wMat_mul_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux4
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux4
theorem _root_.solution {n : ℕ} (M : Matrix (Fin j) (Fin n) ℂ) : G.wMat j * (G.wMat j * M) = M := by
  rw [← Matrix.mul_assoc, wMat_mul_self, Matrix.one_mul]
end Formalism.FourierDecayAlt.P.Ux4
