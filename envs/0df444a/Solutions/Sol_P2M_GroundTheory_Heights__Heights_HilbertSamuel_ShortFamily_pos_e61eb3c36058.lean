-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ShortFamily_pos_e61eb3c36058
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:57:34.315029+00:00
-- url     : https://prove2.me/submissions/76c1378e-1123-47a9-8aa6-836562f25640

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StandardLatticeVecIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ShortFamilyEquivSmallFamilyVec
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_NormFibreVecPosOfLinearIndependent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_norm_fibreVec_pos_of_linearIndependent_9df75dd84b55

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
namespace ShortFamily
theorem _root_.solution {E : HermitianBundle.{0} K} {lam : (K →+* ℂ) → ℝ}
    (F : ShortFamily E lam) (h : 0 < bundleRank E) (σ : K →+* ℂ) : 0 < lam σ := by
  have h1 := norm_fibreVec_pos_of_linearIndependent F.linearIndependent σ ⟨0, h⟩
  have h2 := F.norm_le σ ⟨0, h⟩
  rw [fibreNorm_one_tmul] at h2
  linarith
end ShortFamily
end GroundTheory.Heights₂.Heights.HilbertSamuel
