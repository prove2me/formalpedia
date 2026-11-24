-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_SignAntidiagonal_smul_mem__5661bbd89423
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:19:09.187188+00:00
-- url     : https://prove2.me/submissions/b295e241-f28d-497d-9c83-75719550ff0f

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThirdPolynomialExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstPeelingMinorMemIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants
variable {A : Type} [Ring A] [Algebra ℂ A]
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution (I : Ideal A) (c : ℂ) {x : A} (hx : x ∈ I) : c • x ∈ I := by
  rw [Algebra.smul_def]
  exact I.mul_mem_left _ hx
end Formalism.FourierDecayAlt.P.SignAntidiagonal
