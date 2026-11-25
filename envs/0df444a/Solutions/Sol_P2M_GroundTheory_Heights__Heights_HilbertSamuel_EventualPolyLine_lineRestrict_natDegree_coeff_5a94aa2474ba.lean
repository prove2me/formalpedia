-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolyLine_lineRestrict_natDegree_coeff_5a94aa2474ba
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:30:54.35805+00:00
-- url     : https://prove2.me/submissions/01d901b9-1246-409d-a7a0-f5489de4ec27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsEventualPolyLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PEventualValueFacts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PEventualPolyLine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolyLine_prod_line_pow_7d765d194025

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open Polynomial GroundTheory.Heights₂.Heights.NumbersDVR fwdDiff
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolyLine
variable {K : Type}
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolyLine
theorem _root_.solution [Fintype K] (D : ℕ) (a c : K → ℚ) (p : MvPolynomial K ℚ)
    (hp : p.totalDegree ≤ D) :
    (lineRestrict a c p).natDegree ≤ D ∧ (lineRestrict a c p).coeff D = topCoeff D a p := by
  have hs : ∀ s ∈ p.support, ∑ k, s k ≤ D := fun s hs => by
    have := MvPolynomial.le_totalDegree hs
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at this
    exact this.trans hp
  have hexp : lineRestrict a c p =
      ∑ s ∈ p.support, C (p.coeff s) * ∏ k, (C (a k) * X + C (c k)) ^ (s k) := by
    unfold lineRestrict
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
    rfl
  rw [hexp]
  constructor
  · refine natDegree_sum_le_of_forall_le _ _ (fun s hs' => ?_)
    exact (natDegree_C_mul_le _ _).trans ((prod_line_pow a c s Finset.univ).1.trans (hs s hs'))
  · rw [Polynomial.finsetSum_coeff]
    refine Finset.sum_congr rfl (fun s hs' => ?_)
    rw [Polynomial.coeff_C_mul]
    congr 1
    split_ifs with hD
    · rw [← hD]
      exact (prod_line_pow a c s Finset.univ).2
    · exact coeff_eq_zero_of_natDegree_lt
        ((prod_line_pow a c s Finset.univ).1.trans_lt (lt_of_le_of_ne (hs s hs') hD))
end GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolyLine
