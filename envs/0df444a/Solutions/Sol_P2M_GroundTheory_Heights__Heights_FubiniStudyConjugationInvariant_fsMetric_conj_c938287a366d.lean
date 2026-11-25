-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FubiniStudyConjugationInvariant_fsMetric_conj_c938287a366d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:25:29.852888+00:00
-- url     : https://prove2.me/submissions/6e12e918-3766-46b9-918e-4e3d98cad8fb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PFsConjInvariant

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
open ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.FubiniStudyConjugationInvariant
namespace GroundTheory.Heights₂.Heights.FubiniStudyConjugationInvariant
theorem _root_.solution {n : Type*} [Fintype n] (w : n → ℂ) :
    (fsMetric n).ρ (fun i => (starRingEnd ℂ) (w i)) = (fsMetric n).ρ w := by
  simp [fsMetric, EuclideanSpace.norm_eq]
end GroundTheory.Heights₂.Heights.FubiniStudyConjugationInvariant
