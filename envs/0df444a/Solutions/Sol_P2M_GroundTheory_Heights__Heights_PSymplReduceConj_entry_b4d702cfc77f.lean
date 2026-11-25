-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PSymplReduceConj_entry_b4d702cfc77f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:46:13.945861+00:00
-- url     : https://prove2.me/submissions/7af73306-9f8a-4da3-a11e-f4a4d9e91021

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
theorem _root_.solution {l : Type*} [Fintype l] (E H : Matrix l l ℝ) (x y : l) :
    (E * H * Eᵀ) x y = ∑ w, E x w * ∑ z, E y z * H w z := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring
end GroundTheory.Heights₂.Heights.PSymplReduceConj
