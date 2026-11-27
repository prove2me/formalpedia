-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_InterNumCut_proof_5044aa527abb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:08:14.543957+00:00
-- url     : https://prove2.me/submissions/b585d487-9985-4af7-bf9a-ad6cee3a43e9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StCutRestrLenExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StMixedTwistShift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCycleSplitFilt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCutZeroNotLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TensorSubInsertion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PInterNumCut
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CutZeroNotLe_proof_5cdce7be14c8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ZeroIdealChart_proof_6f00db9dd451
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_KleimanIntersectionNumberCut_proof__9272f1faa9bf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable section
universe u w
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace InterNumCut
theorem _root_.solution (hF : CycleSplit.Filt.Statement.{u, w}) (hA : CutRestrLenExact.Statement.{u, w})
    (hB : MixedTwistShift.Statement.{u, w}) : InterNumCut.Statement.{u, w} :=
  _root_.P2M_UpperTheory_Reformulated_B_KleimanIntersectionNumberCut_proof__9272f1faa9bf hF hA hB
end InterNumCut
end GroundTheory.Heights₂.Heights.Kleiman
