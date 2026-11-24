-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Schur_hsymm_eq_sum_finsuppAntidiag_43772939f291
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:28:22.988982+00:00
-- url     : https://prove2.me/submissions/fb9fdd3d-04a3-410e-a6d7-f3546de18224

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi

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
theorem _root_.solution (n : ℕ) :
    hsymm σ ℚ n = ∑ l ∈ finsuppAntidiag (univ : Finset σ) n, ∏ i, (X i : MvPolynomial σ ℚ) ^ l i := by
  rw [hsymm]
  refine Finset.sum_bij' (fun s _ => Multiset.toFinsupp s.1)
    (fun l hl => (⟨Finsupp.toMultiset l, ?_⟩ : Sym σ n)) ?_ ?_ ?_ ?_ ?_
  · rw [mem_finsuppAntidiag] at hl
    rw [Finsupp.card_toMultiset, Finsupp.sum_fintype _ _ (by simp)]
    exact hl.1
  · intro s _
    rw [mem_finsuppAntidiag]
    refine ⟨?_, subset_univ _⟩
    have := Multiset.toFinsupp_sum_eq s.1
    rw [Finsupp.sum_fintype _ _ (by simp)] at this
    simp only [id] at this
    change ∑ i, (Multiset.toFinsupp s.1) i = n
    rw [this]; exact s.2
  · intro s _; exact mem_univ _
  · intro s _
    apply Subtype.ext
    simp
  · intro l _
    simp
  · intro s _
    rw [Finset.prod_multiset_map_count]
    rw [Finset.prod_subset (subset_univ _)]
    · simp [Multiset.toFinsupp_apply]
    · intro i _ hi
      rw [Multiset.mem_toFinset] at hi
      rw [Multiset.count_eq_zero.mpr hi, pow_zero]
end GroundTheory.Heights₂.Heights.RestTerms.Schur
