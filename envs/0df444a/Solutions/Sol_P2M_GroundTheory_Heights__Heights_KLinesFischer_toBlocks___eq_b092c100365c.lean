-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KLinesFischer_toBlocks___eq_b092c100365c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:00:46.991535+00:00
-- url     : https://prove2.me/submissions/c4975a58-78c9-4146-bf85-f9178eca41ab

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesFischer

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
open Matrix
open scoped ComplexOrder
open GroundTheory.Heights₂.Heights.KLinesFischer
namespace GroundTheory.Heights₂.Heights.KLinesFischer
theorem _root_.solution {m k : Type*} {M : Matrix (m ⊕ k) (m ⊕ k) ℂ} (hM : M.IsHermitian) :
    M.toBlocks₂₁ = M.toBlocks₁₂ᴴ := by
  ext i j
  simp only [toBlocks₂₁, toBlocks₁₂, conjTranspose_apply, of_apply]
  exact (hM.apply (Sum.inr i) (Sum.inl j)).symm
end GroundTheory.Heights₂.Heights.KLinesFischer
