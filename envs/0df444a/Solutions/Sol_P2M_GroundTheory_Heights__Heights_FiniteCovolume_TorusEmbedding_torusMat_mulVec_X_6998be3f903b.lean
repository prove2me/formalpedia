-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_TorusEmbedding_torusMat_mulVec_X_6998be3f903b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:09:53.125256+00:00
-- url     : https://prove2.me/submissions/a066f261-3c0b-481e-b70b-049f74ad38dd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsTorusEmbedding
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PHermAtPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PGramAtData
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PTorusEmbedding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.FiniteCovolume.TorusEmbedding
variable {ι : Type*} [Fintype ι]
variable {H : Matrix ι ι ℂ} {X Y : ι → ℂ}
variable [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.TorusEmbedding
theorem _root_.solution (hXX : pair H X X = 0) (hYX : pair H Y X = 1) (s t : ℂ) :
    torusMat H X Y s t *ᵥ X = s • X := by
  rw [torusMat_mulVec, hYX, hXX]; module
end GroundTheory.Heights₂.Heights.FiniteCovolume.TorusEmbedding
