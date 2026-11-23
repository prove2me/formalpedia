-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_Mx7_xEx_pair__9b8c59969b7c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:48:32.928594+00:00
-- url     : https://prove2.me/submissions/4327c94e-3326-42cd-91d2-3e24b1a27dfa

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_xEx_pair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx7
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
namespace Formalism.FourierDecayAlt.P.Mx7
theorem _root_.solution (P : Par) (π : Ty P) (Y : ℂ) (l j : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l) :
    xEx P {j} π Y = xEx P {l, j} π Y * (Y + (rho P π l : ℂ)) := by
  rw [Finset.pair_comm l j]; exact xEx_pair P π Y j l hl (Ne.symm hjl)
end Formalism.FourierDecayAlt.P.Mx7
