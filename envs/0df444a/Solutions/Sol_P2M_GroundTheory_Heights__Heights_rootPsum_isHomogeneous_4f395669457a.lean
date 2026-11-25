-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_rootPsum_isHomogeneous_4f395669457a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:58:33.399314+00:00
-- url     : https://prove2.me/submissions/3f0c3c8e-8186-4421-856a-02e9c7428d46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutIKillsIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (f j k m : ℕ) (τ : Fin f) :
    (rootPsum f j k m τ).IsHomogeneous m :=
  IsHomogeneous.sum _ _ _ fun _ _ => isHomogeneous_X_pow _ _
end GroundTheory.Heights₂.Heights
