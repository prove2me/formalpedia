-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PSymplReduceStep_symplExt_map_f6dcba10a721
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:46:19.661057+00:00
-- url     : https://prove2.me/submissions/480dc5a1-2da2-44de-a0f2-cde3f686a913

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplReduceStep

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
noncomputable section
open GroundTheory.Heights₂.Heights.PSymplReduceStep
namespace GroundTheory.Heights₂.Heights.PSymplReduceStep
theorem _root_.solution {n : ℕ} (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) :
    (symplExt (1 : ℤ) 0 0 1 Q).map (Int.cast : ℤ → ℝ) =
      symplExt 1 0 0 1 (Q.map (Int.cast : ℤ → ℝ)) := by
  ext x y
  rcases x with i | i <;> rcases y with j | j <;>
    cases i using Fin.cases <;> cases j using Fin.cases <;> simp [symplExt, symplCons]
end GroundTheory.Heights₂.Heights.PSymplReduceStep
