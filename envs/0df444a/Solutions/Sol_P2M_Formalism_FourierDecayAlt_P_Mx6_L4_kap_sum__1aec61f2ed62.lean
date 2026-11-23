-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_Mx6_L4_kap_sum__1aec61f2ed62
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:46.132406+00:00
-- url     : https://prove2.me/submissions/0dcbbe79-e9d4-4284-93bd-8be2086926e9

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6 Formalism.FourierDecayAlt.P.Mx6.L4
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M
noncomputable section
variable (P : Par)
namespace Formalism.FourierDecayAlt.P.Mx6.L4
theorem _root_.solution (s : Finset ℕ) (f : ℕ → Ty P → ℂ) :
    kap P (fun π => ∑ l ∈ s, f l π) = ∑ l ∈ s, kap P (f l) := by
  rw [← map_sum]
  congr 1
  funext π
  simp [Finset.sum_apply]
end Formalism.FourierDecayAlt.P.Mx6.L4
