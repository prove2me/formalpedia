-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_norm_fibreVec_pos_of_linearIndependent_9df75dd84b55
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:56.707457+00:00
-- url     : https://prove2.me/submissions/ffe7ca6e-0a9f-4c65-b0cd-3122f3c4ea23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StandardLatticeVecIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ShortFamilyEquivSmallFamilyVec
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_NormFibreVecPosOfLinearIndependent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open NumberField TensorProduct
noncomputable section
variable {K : Type} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution {E : HermitianBundle.{0} K} {ι : Type*}
    {s : ι → E.carrier} (hs : LinearIndependent (𝓞 K) s) (σ : K →+* ℂ) (i : ι) :
    0 < ‖fibreVec E.metric σ (s i)‖ :=
  norm_pos_iff.mpr ((linearIndependent_fibreVec E.metric σ hs).ne_zero i)
end GroundTheory.Heights₂.Heights.HilbertSamuel
