-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Schur_coeff_omitProduct_eq_zero_d1cd08c82e98
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:24:46.988882+00:00
-- url     : https://prove2.me/submissions/b6b041e1-ef15-4736-bde7-94d2b528e876

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Schur_coeff_prod_one_sub_eq_zero_efeffefc5a98

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Schur
open MvPolynomial Finset
noncomputable section
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
namespace GroundTheory.Heights₂.Heights.RestTerms.Schur
theorem _root_.solution (j : σ) (c : ℕ) (hc : Fintype.card σ ≤ c) :
    PowerSeries.coeff c (omitProduct j) = 0 := by
  apply coeff_prod_one_sub_eq_zero
  rw [card_erase_of_mem (mem_univ j), card_univ]
  have : 0 < Fintype.card σ := Fintype.card_pos_iff.mpr ⟨j⟩
  omega
end GroundTheory.Heights₂.Heights.RestTerms.Schur
