-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PSymplReducePosDef_sum_mul_symplCons_68553baf88f1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:46:18.341268+00:00
-- url     : https://prove2.me/submissions/37fa5c28-4345-45ae-a2e3-4e2d9531316d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplReducePosDef

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
open GroundTheory.Heights₂.Heights.PSymplReducePosDef
namespace GroundTheory.Heights₂.Heights.PSymplReducePosDef
theorem _root_.solution {n : ℕ} (c : ℝ) (x : Fin n ⊕ Fin n → ℝ)
    (F : Fin (n + 1) ⊕ Fin (n + 1) → ℝ) :
    ∑ p, F p * symplCons c 0 x p =
      F (Sum.inl 0) * c + ∑ q, F (Sum.map Fin.succ Fin.succ q) * x q := by
  simp [Fintype.sum_sum_type, Fin.sum_univ_succ, symplCons]
  ring
end GroundTheory.Heights₂.Heights.PSymplReducePosDef
