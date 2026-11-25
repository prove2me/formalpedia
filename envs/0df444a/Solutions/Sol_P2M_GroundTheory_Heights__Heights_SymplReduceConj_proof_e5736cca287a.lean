-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SymplReduceConj_proof_e5736cca287a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:54:17.865936+00:00
-- url     : https://prove2.me/submissions/5a7b9571-63be-4c01-be37-a7a24ecb8c5d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplReduceConj
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplReduceConj_sum_symplCons_7f444f4725ab
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplReduceConj_row_e_4090d0a82855
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplReduceConj_ends_rank_three_of_local_467a38211808
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplReduceConj_entry_b4d702cfc77f

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
open PSymplReduceConj
namespace GroundTheory.Heights₂.Heights
namespace SymplReduceConj
theorem _root_.solution : SymplReduceConj.Statement := by
  intro n H Q
  have kee : (symplExt (1 : ℝ) 0 0 1 Q * H * (symplExt (1 : ℝ) 0 0 1 Q)ᵀ) (Sum.inl 0) (Sum.inl 0) =
      H (Sum.inl 0) (Sum.inl 0) := by
    rw [entry, row_e]
    simp only [sum_symplCons, zero_mul, one_mul, add_zero, Pi.zero_apply, Finset.sum_const_zero]
  refine ⟨kee, ?_⟩
  ext a b
  have kse : (symplExt (1 : ℝ) 0 0 1 Q * H * (symplExt (1 : ℝ) 0 0 1 Q)ᵀ)
      (Sum.map Fin.succ Fin.succ a) (Sum.inl 0) =
      ∑ q, Q a q * H (Sum.map Fin.succ Fin.succ q) (Sum.inl 0) := by
    rw [entry, ends_rank_three_of_local, row_e]
    simp only [sum_symplCons, zero_mul, one_mul, add_zero, zero_add, Pi.zero_apply,
      Finset.sum_const_zero]
  have kes : (symplExt (1 : ℝ) 0 0 1 Q * H * (symplExt (1 : ℝ) 0 0 1 Q)ᵀ)
      (Sum.inl 0) (Sum.map Fin.succ Fin.succ b) =
      ∑ r, Q b r * H (Sum.inl 0) (Sum.map Fin.succ Fin.succ r) := by
    rw [entry, ends_rank_three_of_local, row_e]
    simp only [sum_symplCons, zero_mul, one_mul, add_zero, zero_add, Pi.zero_apply,
      Finset.sum_const_zero]
  have kss : (symplExt (1 : ℝ) 0 0 1 Q * H * (symplExt (1 : ℝ) 0 0 1 Q)ᵀ)
      (Sum.map Fin.succ Fin.succ a) (Sum.map Fin.succ Fin.succ b) =
      ∑ q, Q a q * ∑ r, Q b r * H (Sum.map Fin.succ Fin.succ q) (Sum.map Fin.succ Fin.succ r) := by
    rw [entry, ends_rank_three_of_local, ends_rank_three_of_local]
    simp only [sum_symplCons, zero_mul, add_zero, zero_add]
  show _ - _ * _ / _ = _
  rw [kss, kse, kes, kee]
  calc _ = ∑ q, ∑ r, Q a q * symplReduce H q r * Q b r := by
        rw [Finset.sum_mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun r _ => ?_
        simp only [symplReduce]
        ring
    _ = _ := by
        simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
        exact Finset.sum_comm
end SymplReduceConj
end GroundTheory.Heights₂.Heights
