-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_blockOut_rect_2840281a3f1e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:53:40.543314+00:00
-- url     : https://prove2.me/submissions/807556e3-fb61-44ec-a774-ba598b366682

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_BlockValue
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_mem_partitionsOf_iff_9f8ef15178d9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_rectangle_mem_partitionsOf_35563b48a979
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_schur_zero_cf6b31ecc1ca


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
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Top
theorem _root_.solution (r a : ℕ) (c : SmallBlock) (κ : ℚ) (q m : ℕ) (h : q + m = r * a) :
    blockOut r a c κ q m = C (blockCoeff q m (rectangle r a) * κ) := by
  rw [blockOut, Finset.sum_eq_single (rectangle r a)]
  · have h0 : (fun i : Fin r => rectangle r a i - a) = 0 := funext fun i => by simp [rectangle]
    rw [pushOut, if_pos (fun i => by simp [rectangle]), h0, schur_zero, map_one, mul_one, smul_eq_C_mul,
      ← C_mul, mul_comm]
  · intro lam hlam hne
    rw [pushOut, if_neg, smul_zero]
    intro hall
    apply hne
    rw [mem_partitionsOf_iff] at hlam
    have h1 : ∑ i, (lam i - a) + ∑ i : Fin r, a = ∑ i, lam i := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hall i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
    have h2 : ∑ i, (lam i - a) = 0 := by omega
    funext i
    have := Finset.sum_eq_zero_iff.mp h2 i (Finset.mem_univ i)
    have := hall i
    simp only [rectangle]
    omega
  · intro h'
    exact absurd ((rectangle_mem_partitionsOf r a _).mpr h) h'
end GroundTheory.Heights₂.Heights.RestTerms.Top
