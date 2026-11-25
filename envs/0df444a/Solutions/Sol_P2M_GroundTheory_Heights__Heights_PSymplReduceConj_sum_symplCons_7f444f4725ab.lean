-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PSymplReduceConj_sum_symplCons_7f444f4725ab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:46:17.712364+00:00
-- url     : https://prove2.me/submissions/1abe80d1-8df6-444c-ae8e-a253c9a2f091

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplReduceConj

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
open GroundTheory.Heights₂.Heights.PSymplReduceConj
namespace GroundTheory.Heights₂.Heights.PSymplReduceConj
theorem _root_.solution {n : ℕ} (p q : ℝ) (w : Fin n ⊕ Fin n → ℝ)
    (F : Fin (n + 1) ⊕ Fin (n + 1) → ℝ) :
    ∑ x, symplCons p q w x * F x =
      p * F (Sum.inl 0) + q * F (Sum.inr 0) + ∑ y, w y * F (Sum.map Fin.succ Fin.succ y) := by
  simp [symplCons, Fintype.sum_sum_type, Fin.sum_univ_succ]
  ring
end GroundTheory.Heights₂.Heights.PSymplReduceConj
