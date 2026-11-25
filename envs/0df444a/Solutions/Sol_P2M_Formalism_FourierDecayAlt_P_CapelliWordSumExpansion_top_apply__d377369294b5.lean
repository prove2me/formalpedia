-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_top_apply__d377369294b5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:37:16.336331+00:00
-- url     : https://prove2.me/submissions/1ab6bc72-891f-4251-8b6a-047aa9d2da88

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
theorem _root_.solution (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))
    (u : ℂ) (c d : Fin (2 * r + k + 1)) (f : Mat k r → E) (g : Mat k r) :
    Top Eop u c d f g = (if c = d then u • f g else 0) + Eop c d f g := rfl
end Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
