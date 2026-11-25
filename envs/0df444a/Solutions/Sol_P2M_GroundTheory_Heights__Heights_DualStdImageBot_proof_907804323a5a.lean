-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualStdImageBot_proof_907804323a5a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:32:28.12849+00:00
-- url     : https://prove2.me/submissions/9be2a015-2664-40a9-8544-b994340a714f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_SingleMemDualLatticeStandard
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdImageBot
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualImageBottom_evalQ_graphMap_b8a03b5fa4fa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualImageBottom_aeval_genPt_injective_334eaaac816a

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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial
noncomputable section
open StandardDualImageBottom
namespace GroundTheory.Heights₂.Heights
namespace DualStdImageBot
theorem _root_.solution : DualStdImageBot.Statement := by
  intro K _ _ i T _ _ b
  refine eq_bot_iff.mpr fun f hf => (Ideal.mem_bot).mpr (aeval_genPt_injective (K := K) (i := i) ?_)
  have h0 : graphMap (dualIdeal b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b))
      (rename (inrV (ι := dualBlocks T) (ι₂ := PBlk i)) f) = 0 := hf
  rw [map_zero, ← evalQ_graphMap b, h0, map_zero]
end DualStdImageBot
end GroundTheory.Heights₂.Heights
