-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_SymmFun_eval_hsymm_04c692b73247
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:43:43.3968+00:00
-- url     : https://prove2.me/submissions/9c6769bd-3e4e-4c60-9ea3-35131d864879

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_Capelli_CompleteHomogeneous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.SymmFun
open MvPolynomial Finset
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
namespace GroundTheory.Heights₂.Theta.SymmFun
theorem _root_.solution (x : σ → ℂ) (b : ℕ) :
    eval x (hsymm σ ℂ b) = ∑ l ∈ finsuppAntidiag (univ : Finset σ) b, ∏ i, x i ^ l i := by
  rw [hsymm, map_sum]
  refine Finset.sum_bij' (fun s _ => Multiset.toFinsupp s.1)
    (fun l hl => ⟨Finsupp.toMultiset l, by
      rw [Finsupp.card_toMultiset, Finsupp.sum_fintype _ _ (by simp)]
      exact (mem_finsuppAntidiag.mp hl).1⟩) ?_ ?_ ?_ ?_ ?_
  · intro s _
    rw [mem_finsuppAntidiag]
    refine ⟨?_, by simp⟩
    have := Multiset.toFinsupp_sum_eq s.1
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at this
    exact this.trans s.2
  · intro l _
    exact Finset.mem_univ _
  · intro s _
    ext1
    simp
  · intro l _
    simp
  · intro s _
    rw [map_multiset_prod, Multiset.map_map, Finset.prod_multiset_map_count]
    rw [Finset.prod_subset (Finset.subset_univ _)]
    · refine Finset.prod_congr rfl fun i _ => ?_
      simp [Multiset.toFinsupp_apply]
    · intro i _ hi
      rw [Multiset.mem_toFinset] at hi
      rw [Multiset.count_eq_zero.mpr hi, pow_zero]
end GroundTheory.Heights₂.Theta.SymmFun
