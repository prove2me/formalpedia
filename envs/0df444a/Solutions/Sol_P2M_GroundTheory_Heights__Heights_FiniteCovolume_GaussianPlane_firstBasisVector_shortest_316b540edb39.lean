-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_firstBasisVector_shortest_316b540edb39
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:01:17.499947+00:00
-- url     : https://prove2.me/submissions/6d9c8fa8-0fbe-419f-9337-3f0b514fc50f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianDisc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_Examples
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_one_le_len_e9003551bcf2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_majorantLength_firstBasisVector_400e0bce7725

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
theorem _root_.solution (y : Fin 2 → Eg) (hy : y ∈ LaG) (hy0 : y ≠ 0) :
    MG.len (invApply (1 : archUnitary hG vG) (vecAt vG e0)) ≤
      MG.len (invApply (1 : archUnitary hG vG) (vecAt vG y)) := by
  rw [majorantLength_firstBasisVector]
  exact one_le_len hy hy0
end GroundTheory.Heights₂.Heights.FiniteCovolume.GaussianPlane
