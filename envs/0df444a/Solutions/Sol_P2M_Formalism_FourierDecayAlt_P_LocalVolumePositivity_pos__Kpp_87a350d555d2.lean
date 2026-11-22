-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_LocalVolumePositivity_pos__Kpp_87a350d555d2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:15:03.746964+00:00
-- url     : https://prove2.me/submissions/9044a31d-ad94-48e9-9e1b-35422928f093

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Formalism.FourierDecayAlt.S3
open Formalism.FourierDecayAlt.P.LocalVolumePositivity
variable {P : Type} [Fintype P] {B : MassData P}
namespace Formalism.FourierDecayAlt.P.LocalVolumePositivity
theorem _root_.solution (hP : B.Pos) : 0 < B.μKpp := by
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  unfold MassData.μKpp
  exact mul_pos xKo (prod_pos fun p _ => (hp p).2.2.2.2.2.2.2.1)
end Formalism.FourierDecayAlt.P.LocalVolumePositivity
