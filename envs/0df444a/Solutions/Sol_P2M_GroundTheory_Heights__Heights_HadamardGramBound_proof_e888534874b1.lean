-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HadamardGramBound_proof_e888534874b1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:54:46.809736+00:00
-- url     : https://prove2.me/submissions/43a48eaf-b230-4322-8a58-6ef0119ff238

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_DetGramLeProdNormSq
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HadamardGramBound_det_gram_le_prod_norm_sq_08823bc1ad4b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HadamardGramBound_gram_comb_bc947bb4ac6f

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
theorem _root_.solution : HadamardGramBound.Statement := by
  intro V _ _ r v b hv hn hb
  choose M hM using fun i => (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hb i)
  set N : Matrix (Fin r) (Fin r) ℝ := (Matrix.of M).map (Int.cast : ℤ → ℝ) with hNdef
  have hvN : v = fun i => ∑ j, N i j • b j := by
    funext i
    rw [← hM i]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [N, Int.cast_smul_eq_zsmul]
  have hG : Matrix.gram ℝ v = N * Matrix.gram ℝ b * N.transpose := by
    rw [hvN]
    exact gram_comb N b
  have hdet : (Matrix.gram ℝ v).det = N.det ^ 2 * (Matrix.gram ℝ b).det := by
    rw [hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    ring
  have hvpos : 0 < (Matrix.gram ℝ v).det := (Matrix.posDef_gram_of_linearIndependent hv).det_pos
  have hbnn : 0 ≤ (Matrix.gram ℝ b).det := (Matrix.posSemidef_gram ℝ b).det_nonneg
  have hNdet : N.det = (((Matrix.of M).det : ℤ) : ℝ) := by
    rw [hNdef]
    exact ((Int.castRingHom ℝ).map_det (Matrix.of M)).symm
  have hN0 : N.det ≠ 0 := by
    intro h
    rw [hdet, h] at hvpos
    simp at hvpos
  have hN1 : 1 ≤ N.det ^ 2 := by
    rw [hNdet] at hN0 ⊢
    have hd : (Matrix.of M).det ≠ 0 := by exact_mod_cast hN0
    have : (1 : ℤ) ≤ (Matrix.of M).det ^ 2 := by
      rcases lt_or_gt_of_ne hd with h | h <;> nlinarith
    exact_mod_cast this
  have hHad := det_gram_le_prod_norm_sq v hv
  have hprod : ∏ i, ‖v i‖ ^ 2 ≤ 1 :=
    Finset.prod_le_one (fun i _ => sq_nonneg _) fun i _ => pow_le_one₀ (norm_nonneg _) (hn i)
  change 0 < (Matrix.gram ℝ b).det ∧ (Matrix.gram ℝ b).det ≤ 1
  refine ⟨lt_of_le_of_ne hbnn fun h => ?_, ?_⟩
  · rw [hdet, ← h] at hvpos
    simp at hvpos
  · nlinarith
end GroundTheory.Heights₂.Heights.HadamardGramBound
