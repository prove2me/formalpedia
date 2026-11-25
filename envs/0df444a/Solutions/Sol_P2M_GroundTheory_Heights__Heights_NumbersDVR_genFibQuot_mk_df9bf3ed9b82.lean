-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_genFibQuot_mk_df9bf3ed9b82
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:42:17.488837+00:00
-- url     : https://prove2.me/submissions/09b74ec7-4c2e-45ac-89d9-2f24a21ffe95

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericPieceRank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
variable {O : Type*} [CommRing O] [IsDomain O] {K : Type*} [DecidableEq K] {ι : K → Type*}
omit [IsDomain O] [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (P : Ideal (MRing ι O)) (g : MRing ι O) :
    genFibQuot P (Ideal.Quotient.mk P g) =
      Ideal.Quotient.mk (genFib P) (map (algebraMap O (FractionRing O)) g) := rfl
end GroundTheory.Heights₂.Heights.NumbersDVR
