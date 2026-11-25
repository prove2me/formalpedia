-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IncidenceZeroLocus_eval__eq_sum_degree_5c698ff6417a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:56:00.279588+00:00
-- url     : https://prove2.me/submissions/4edca4c0-fa27-446a-8bc4-5037cec36468

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsIncidenceZeroLocus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PIncidenceZeroLocus
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IncidenceZeroLocus_mem_finsuppAntidiag_univ_iff_5c8a1f46e0c6

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.IncidenceZeroLocus
namespace GroundTheory.Heights₂.Heights.IncidenceZeroLocus
theorem _root_.solution {R S : Type*} [CommSemiring R] [CommSemiring S] {n N : ℕ} (g : R →+* S)
    (x : Fin n → S) (p : MvPolynomial (Fin n) R) (hp : p.IsHomogeneous N) :
    eval₂ g x p = ∑ f : ((Finset.univ : Finset (Fin n)).finsuppAntidiag N),
      g (coeff (f : Fin n →₀ ℕ) p) * ∏ j, x j ^ (f : Fin n →₀ ℕ) j := by
  rw [eval₂_eq', Finset.sum_coe_sort ((Finset.univ : Finset (Fin n)).finsuppAntidiag N)
    (fun f => g (coeff f p) * ∏ j, x j ^ f j)]
  refine Finset.sum_subset (fun d hd => ?_) (fun d _ hd => ?_)
  · have h := hp (mem_support_iff.mp hd)
    rw [mem_finsuppAntidiag_univ_iff, Finsupp.degree_eq_weight_one]
    exact h
  · rw [notMem_support_iff.mp hd, map_zero, zero_mul]
end GroundTheory.Heights₂.Heights.IncidenceZeroLocus
