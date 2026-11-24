-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_FourTermExpansion_top_apply___a095e6ea583d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:28:49.525484+00:00
-- url     : https://prove2.me/submissions/f66489b8-3143-44c8-b8b6-3a4b081f1c29

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FourTermExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (M : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Mat k r)
namespace Formalism.FourierDecayAlt.P.FourTermExpansion
theorem _root_.solution (v : ℂ) (a b : Fin (2 * r + k + 1)) (Φ : Mat k r → E) (g : Mat k r) :
    Top (LT M) v a b Φ g = (if a = b then v • Φ g else 0) + EZ (M a b) Φ g := rfl
end Formalism.FourierDecayAlt.P.FourTermExpansion
