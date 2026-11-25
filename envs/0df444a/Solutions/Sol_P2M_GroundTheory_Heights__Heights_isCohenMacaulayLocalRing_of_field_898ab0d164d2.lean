-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isCohenMacaulayLocalRing_of_field_898ab0d164d2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:32:59.536384+00:00
-- url     : https://prove2.me/submissions/0edcf777-8304-476b-b574-7572e1ca0abf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTransverseObjects

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
open MvPolynomial Matrix ComplexSets IsLocalRing
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (K : Type*) [Field K] : IsCohenMacaulayLocalRing K where
  exists_isWeaklyRegular := ⟨[], by simp, RingTheory.Sequence.IsWeaklyRegular.nil K K, by
    simp [ringKrullDim_eq_zero_of_field]⟩
end GroundTheory.Heights₂.Heights
