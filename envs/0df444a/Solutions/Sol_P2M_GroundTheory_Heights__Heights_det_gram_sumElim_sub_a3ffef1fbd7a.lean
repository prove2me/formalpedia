-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_det_gram_sumElim_sub_a3ffef1fbd7a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:37:48.121705+00:00
-- url     : https://prove2.me/submissions/ca1380d4-644d-4ab2-b0c3-8ed77a68f487

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Extension

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
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (v : ι → V) (u : κ → V) (M : Matrix ι κ ℂ) :
    det (gram ℂ (Sum.elim v (fun j ↦ u j - ∑ i, M i j • v i))) = det (gram ℂ (Sum.elim v u)) := by
  set B : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ := fromBlocks 1 (-M) 0 1 with hBdef
  have hc : Sum.elim v (fun j ↦ u j - ∑ i, M i j • v i) =
      fun b ↦ ∑ a, B a b • Sum.elim v u a := by
    funext b
    rcases b with i | j
    · simp [B, Fintype.sum_sum_type, one_apply, ite_smul]
    · simp [B, Fintype.sum_sum_type, one_apply, ite_smul, sub_eq_add_neg, add_comm]
  have hB : det B = 1 := by simp [B]
  rw [hc, gram_comb, det_mul, det_mul, det_conjTranspose, hB]
  simp
end GroundTheory.Heights₂.Heights
