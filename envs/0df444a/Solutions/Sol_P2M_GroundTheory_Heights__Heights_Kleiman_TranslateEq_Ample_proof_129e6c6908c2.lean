-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_Ample_proof_129e6c6908c2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:58:58.823832+00:00
-- url     : https://prove2.me/submissions/a29d7f30-e08b-4c88-a28c-4d88a963cf50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsLastLast
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwinEqAmple
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_Generated_equiv_67711faab90f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_GradedMod_equiv_bab59235570c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_IsGradedHom_equiv_a15063e9bd3b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_PrimeFiltration_equiv_055a468f012b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_bundleA_equiv_9a6f65d8882f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_chartModule_of_ne_zero_902c51d3fd20
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_chartRingI_equiv_6c221ab935ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_chartRing_equiv_3295007ad279
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_dimCl_equiv_c39cbd206b03
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_lineX_equiv_6acfbe997019
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_lmul_equiv_a9ac80d74948
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_lpow_equiv_da141a3f94b8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_polyGraded_equiv_07714b7c3c16
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_pow_zero_sub_b7a88b6ce0bd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_secs_equiv_51d02eb19002
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_span_image2_eq_67f8a4da0bc8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_twist_equiv_61178bbb85a9


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
namespace Ample
theorem _root_.solution : Ample.Statement := by
  intro S _ N Ω _ _ x H A
  have hxI : ∀ I : Kleiman.Chart x, ∃ i ∈ I.1, x i ≠ 0 := fun I =>
    let ⟨i, hi⟩ := I.2.1
    ⟨i, hi, (Kleiman.mem_support x).mp (I.2.2 hi)⟩
  have hsub : ∀ k I, A.h k ∈ (H.pow A.m).sub I := by
    intro k I
    have := A.mem_secs k
    rw [Kleiman.SubSystem.secs, Submodule.mem_iInf] at this
    exact this I
  refine ⟨{ m := A.m, m_pos := A.m_pos, M := A.r, h := A.h, gen := ⟨?_, ?_⟩, finite := ?_ }⟩
  · intro k
    simp only [IndefiniteRowSideFullHecke.Kleiman.secs, Submodule.mem_iInf]
    intro i hi
    rw [lpow.equiv _ A.m_pos hi, chartModule_of_ne_zero _ hi, Submodule.restrictScalars_mem]
    exact hsub k _
  · intro i hi
    rw [lpow.equiv _ A.m_pos hi, chartModule_of_ne_zero _ hi, chartRing.equiv S x hi, span_image2_eq,
      A.generates]
  · intro j hj
    obtain ⟨t, ht⟩ := A.finite j hj
    have hle : IndefiniteRowSideFullHecke.Kleiman.regOn S x (toIndefiniteRowSideFullHecke H.toSubSystem) A.m A.h j ≤
        ampleSub H.toSubSystem A.m (A.h j) (hsub j) := by
      rw [IndefiniteRowSideFullHecke.Kleiman.regOn, Algebra.adjoin_le_iff]
      intro f hf
      show f ∈ Kleiman.ampleRing H.toSubSystem A.m (A.h j)
      refine Set.mem_iInter.mpr fun I => ?_
      obtain ⟨i, hiI, hi⟩ := hxI I
      obtain ⟨n, hn⟩ := hf i hi
      refine ⟨n, ?_⟩
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · simp only [pow_zero, mul_one, Submodule.mem_one] at hn
        obtain ⟨s, rfl⟩ := hn
        rw [pow_zero, mul_one, Nat.mul_zero, pow_zero_sub]
        exact Subalgebra.algebraMap_mem _ s
      · have key : IndefiniteRowSideFullHecke.Kleiman.lpow S (toIndefiniteRowSideFullHecke H.toSubSystem) A.m i ^ n =
            IndefiniteRowSideFullHecke.Kleiman.lpow S (toIndefiniteRowSideFullHecke H.toSubSystem) (A.m * n) i := by
          simp only [IndefiniteRowSideFullHecke.Kleiman.lpow, pow_mul]
        rw [key, lpow.equiv _ (Nat.mul_pos A.m_pos hn0) hi, chartModule_of_ne_zero _ hi,
          Submodule.restrictScalars_mem] at hn
        exact (H.pow (A.m * n)).mono _ I (Finset.singleton_subset_iff.mpr hiI) _ hn
    exact ⟨t, fun f hf => ht (hle hf)⟩
end Ample
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
