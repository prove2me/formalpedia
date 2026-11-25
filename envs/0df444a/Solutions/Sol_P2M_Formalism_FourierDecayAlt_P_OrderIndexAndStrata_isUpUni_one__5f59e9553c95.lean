-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_OrderIndexAndStrata_isUpUni_one__5f59e9553c95
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:38:02.349614+00:00
-- url     : https://prove2.me/submissions/984a0b71-0d14-4a85-be49-ee87f5d9d8a2

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrderIndexAndStrata

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrderIndexAndStrata
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni)
open Formalism.FourierDecayAlt.S3
namespace Formalism.FourierDecayAlt.P.OrderIndexAndStrata
theorem _root_.solution {A : Type} [CommRing A] {n : ℕ} : IsUpUni (1 : Matrix (Fin n) (Fin n) A) := by
  exact Formalism.DoubleCosetMeasures.isUpUni_one (K := A)
end Formalism.FourierDecayAlt.P.OrderIndexAndStrata
