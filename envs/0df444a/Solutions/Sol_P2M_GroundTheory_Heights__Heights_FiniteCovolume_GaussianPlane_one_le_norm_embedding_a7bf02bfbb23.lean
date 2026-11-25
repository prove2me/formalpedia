-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_one_le_norm_embedding_a7bf02bfbb23
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:11:26.103323+00:00
-- url     : https://prove2.me/submissions/535bd3dd-5376-4f10-b572-1f8fe9443628

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianDisc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_Examples

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Heights₂.Heights.FiniteCovolume.GaussianPlane
open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped Pointwise ComplexOrder ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.GaussianPlane
theorem _root_.solution (w : InfinitePlace Eg) {a : 𝓞 Eg} (ha : a ≠ 0) :
    1 ≤ ‖w.embedding (a : Eg)‖ := by
  rw [InfinitePlace.norm_embedding_eq]
  exact InfinitePlace.one_le_of_lt_one ha fun z hz => absurd (Subsingleton.elim z w) hz
end GroundTheory.Heights₂.Heights.FiniteCovolume.GaussianPlane
