-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_JCx1_needs_isEmptyReal__0ad2130fa206
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:38:11.315595+00:00
-- url     : https://prove2.me/submissions/d7f4b38f-65f6-45ca-a64c-860e03767ffc

import Definitions.Def_Formalism_HermitianCurvature_StatementJC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism.FourierDecayAlt
open Formalism.FourierDecayAlt Filter Topology MeasureTheory NumberField
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JCx1 Formalism.FourierDecayAlt.P.JCx1.needs
noncomputable section
open scoped Classical
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
namespace Formalism.FourierDecayAlt.P.JCx1.needs
theorem _root_.solution : IsEmpty {w : InfinitePlace E // w.IsReal} := by
  exact ⟨fun w => NumberField.InfinitePlace.not_isReal_iff_isComplex.2
    (NumberField.IsTotallyComplex.isComplex w.1) w.2⟩
end Formalism.FourierDecayAlt.P.JCx1.needs
