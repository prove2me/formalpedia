-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_dividedDifferenceExpansion_term_eq_b68ba4cef9fc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:23:02.853412+00:00
-- url     : https://prove2.me/submissions/0e2f13fb-e8e9-447c-8cc6-7ddeff3cda43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinDivDiffExpansion
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_dividedDifferenceExpansion_prod_split_70d0fbdbab85

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR.dividedDifferenceExpansion
namespace GroundTheory.Heights₂.Heights.NumbersDVR.dividedDifferenceExpansion
theorem _root_.solution {r : ℕ} (μ : Fin r →₀ ℕ) (l : Fin r) :
    (X (Sum.inl l) - X (Sum.inr l) : MvPolynomial (Fin r ⊕ Fin r) ℤ) *
      ((∏ j ∈ Finset.univ.filter (fun j => j < l), X (Sum.inr j) ^ μ j) *
        (∑ a ∈ Finset.range (μ l), X (Sum.inl l) ^ a * X (Sum.inr l) ^ (μ l - 1 - a)) *
        ∏ j ∈ Finset.univ.filter (fun j => l < j), X (Sum.inl j) ^ μ j) =
      stair μ l - stair μ (l + 1) := by
  have hg : (X (Sum.inl l) - X (Sum.inr l) : MvPolynomial (Fin r ⊕ Fin r) ℤ) *
      (∑ a ∈ Finset.range (μ l), X (Sum.inl l) ^ a * X (Sum.inr l) ^ (μ l - 1 - a)) =
      X (Sum.inl l) ^ μ l - X (Sum.inr l) ^ μ l := by
    rw [mul_comm]
    exact geom_sum₂_mul _ _ _
  have hlo : ∀ k : ℕ, (l : ℕ) ≤ k →
      ∏ j ∈ Finset.univ.filter (fun j => j < l),
          (X (if (j : ℕ) < k then Sum.inr j else Sum.inl j) : MvPolynomial (Fin r ⊕ Fin r) ℤ) ^ μ j =
        ∏ j ∈ Finset.univ.filter (fun j => j < l), X (Sum.inr j) ^ μ j := by
    intro k hk
    refine Finset.prod_congr rfl fun j hj => ?_
    have hj' : (j : ℕ) < l := Fin.lt_def.mp (Finset.mem_filter.mp hj).2
    rw [if_pos (by omega)]
  have hhi : ∀ k : ℕ, k ≤ (l : ℕ) + 1 →
      ∏ j ∈ Finset.univ.filter (fun j => l < j),
          (X (if (j : ℕ) < k then Sum.inr j else Sum.inl j) : MvPolynomial (Fin r ⊕ Fin r) ℤ) ^ μ j =
        ∏ j ∈ Finset.univ.filter (fun j => l < j), X (Sum.inl j) ^ μ j := by
    intro k hk
    refine Finset.prod_congr rfl fun j hj => ?_
    have hj' : (l : ℕ) < j := Fin.lt_def.mp (Finset.mem_filter.mp hj).2
    rw [if_neg (by omega)]
  unfold stair
  rw [prod_split l, prod_split l (fun j => (X (if (j : ℕ) < (l : ℕ) + 1 then Sum.inr j else Sum.inl j) :
      MvPolynomial (Fin r ⊕ Fin r) ℤ) ^ μ j), hlo l le_rfl, hlo (l + 1) (by omega),
    hhi l (by omega), hhi (l + 1) le_rfl, if_neg (lt_irrefl _), if_pos (Nat.lt_succ_self _)]
  linear_combination
    ((∏ j ∈ Finset.univ.filter (fun j => j < l), (X (Sum.inr j) : MvPolynomial (Fin r ⊕ Fin r) ℤ) ^ μ j) *
      ∏ j ∈ Finset.univ.filter (fun j => l < j), X (Sum.inl j) ^ μ j) * hg
end GroundTheory.Heights₂.Heights.NumbersDVR.dividedDifferenceExpansion
