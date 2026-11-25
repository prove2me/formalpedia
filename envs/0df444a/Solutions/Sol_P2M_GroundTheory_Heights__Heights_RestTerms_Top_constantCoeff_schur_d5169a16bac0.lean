-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_constantCoeff_schur_d5169a16bac0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:45.805462+00:00
-- url     : https://prove2.me/submissions/f1e73a33-6e60-4b42-b45b-94f7a65b41d4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_schur_zero_cf6b31ecc1ca
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_constantCoeff_completeSymmetric_010966416004

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
theorem _root_.solution (σ : Type*) [Fintype σ] [DecidableEq σ] {m : ℕ} (ν : Fin m → ℕ)
    (hν : Antitone ν) : constantCoeff (schur σ ν) = if ν = 0 then 1 else 0 := by
  split_ifs with h
  · subst h; rw [schur_zero, map_one]
  · have hm : 0 < m := by
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm; exact absurd (funext fun i => i.elim0) h
      · exact hm
    have h0 : 0 < ν ⟨0, hm⟩ := by
      by_contra h0
      refine h (funext fun i => ?_)
      have := hν (show (⟨0, hm⟩ : Fin m) ≤ i from Nat.zero_le _)
      simp only [Pi.zero_apply]
      omega
    unfold schur
    rw [RingHom.map_det]
    apply Matrix.det_eq_zero_of_row_eq_zero ⟨0, hm⟩
    intro j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
      constantCoeff_completeSymmetric]
    rw [if_neg]
    simp only [Nat.cast_zero, sub_zero]
    omega
end GroundTheory.Heights₂.Heights.RestTerms.Top
