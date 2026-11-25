-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_B2x3_Jm__b_3f1be2078428
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:37:12.829602+00:00
-- url     : https://prove2.me/submissions/010e77f9-1c82-41ed-8bc7-4906c38d01bf

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x3
theorem _root_.solution : Jm (εb k) = Hb k := by
  unfold Jm Hb εb
  congr 1
  funext j
  by_cases h : j = Fin.last k <;> simp [h]
end Formalism.FourierDecayAlt.P.B2x3
