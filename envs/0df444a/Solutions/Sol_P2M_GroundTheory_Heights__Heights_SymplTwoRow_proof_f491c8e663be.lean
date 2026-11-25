-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SymplTwoRow_proof_f491c8e663be
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:28:41.127242+00:00
-- url     : https://prove2.me/submissions/09eaeb3a-6ce4-4bec-928e-734c2c4b6b9b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplTwoRow
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplTwoRow_twoBlock_mul_transpose_ada040d03966

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
open PSymplTwoRow
namespace GroundTheory.Heights₂.Heights
namespace SymplTwoRow
theorem _root_.solution : SymplTwoRow.Statement := by
  intro n c d x y h
  refine ⟨fromBlocks (twoBlock n c d x y) 0 0 (twoBlock n x y c d), ?_, ?_⟩
  · rw [SymplecticGroup.mem_iff]
    have h1 := twoBlock_mul_transpose (n := n) h
    have h2 : twoBlock n x y c d * (twoBlock n c d x y)ᵀ = 1 := by
      rw [← transpose_transpose (twoBlock n x y c d), ← transpose_mul, h1, transpose_one]
    simp [J, fromBlocks_transpose, fromBlocks_multiply, h1, h2]
  · funext z
    rcases z with i | i
    · refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
        simp [symplCons, twoBlock]
    · refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
        simp [symplCons]
end SymplTwoRow
end GroundTheory.Heights₂.Heights
