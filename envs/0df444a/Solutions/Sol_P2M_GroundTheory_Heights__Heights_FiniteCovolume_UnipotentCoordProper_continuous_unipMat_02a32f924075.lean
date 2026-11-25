-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentCoordProper_continuous_unipMat_02a32f924075
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:10:30.37286+00:00
-- url     : https://prove2.me/submissions/d7b9e153-7e4b-4cd7-9af7-9491ce9fca70

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StUnipotentCoordProper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PHermAtPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentCoordProper

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology
noncomputable section
open GroundTheory.Heights₂.Heights.FiniteCovolume.UnipotentCoordProper
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.UnipotentCoordProper
theorem _root_.solution (H : Matrix ι ι ℂ) (X W₀ : ι → ℂ) :
    Continuous (unipMat H X W₀) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have hc : Continuous fun u => unipVec H X W₀ u (Pi.single j 1) := by
    unfold unipVec
    apply Continuous.sub
    · exact continuous_const.add (continuous_const_smul _)
    · exact (continuous_star.dotProduct continuous_const).smul continuous_const
  exact (continuous_apply i).comp hc
end GroundTheory.Heights₂.Heights.FiniteCovolume.UnipotentCoordProper
