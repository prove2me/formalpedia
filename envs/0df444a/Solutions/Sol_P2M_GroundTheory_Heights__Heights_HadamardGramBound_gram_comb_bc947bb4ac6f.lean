-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HadamardGramBound_gram_comb_bc947bb4ac6f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:25:28.391634+00:00
-- url     : https://prove2.me/submissions/5d5b831f-c5b6-42c9-9f10-8b5e91f65047

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_DetGramLeProdNormSq

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
open GroundTheory.Heights₂.Heights.HadamardGramBound
namespace GroundTheory.Heights₂.Heights.HadamardGramBound
theorem _root_.solution {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {r : ℕ}
    (M : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → V) :
    Matrix.gram ℝ (fun i => ∑ j, M i j • b j) = M * Matrix.gram ℝ b * M.transpose := by
  ext i k
  simp only [Matrix.gram_apply, Matrix.mul_apply, Matrix.transpose_apply, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
end GroundTheory.Heights₂.Heights.HadamardGramBound
