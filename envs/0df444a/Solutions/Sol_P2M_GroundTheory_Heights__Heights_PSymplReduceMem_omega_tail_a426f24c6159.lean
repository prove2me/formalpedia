-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PSymplReduceMem_omega_tail_a426f24c6159
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:46:25.523269+00:00
-- url     : https://prove2.me/submissions/62168de2-fda7-436f-b9c9-4a1e38c9a41e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplReduceMem

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
open GroundTheory.Heights₂.Heights.PSymplReduceMem
namespace GroundTheory.Heights₂.Heights.PSymplReduceMem
theorem _root_.solution (h2 : SymplCons.Statement) {n : ℕ} (x y : Fin (n + 1) ⊕ Fin (n + 1) → ℝ) :
    symplOmega (symplTail x) (symplTail y) =
      symplOmega x y - (x (Sum.inr 0) * y (Sum.inl 0) - x (Sum.inl 0) * y (Sum.inr 0)) := by
  have key := (h2 ℝ n).2 (x (Sum.inl 0)) (x (Sum.inr 0)) (y (Sum.inl 0)) (y (Sum.inr 0))
    (symplTail x) (symplTail y)
  rw [(h2 ℝ n).1 x, (h2 ℝ n).1 y] at key
  linarith
end GroundTheory.Heights₂.Heights.PSymplReduceMem
