-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_eval__mul_of_isHomogeneous_9f11237f1c08
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:22:59.160714+00:00
-- url     : https://prove2.me/submissions/77b968ea-5f4b-4954-a21c-94fdd8825a7b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGenSecDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.GenSecDomain
namespace GroundTheory.Heights₂.Heights.Vertical.GenSecDomain
theorem _root_.solution {k S : Type*} [CommSemiring k] [CommSemiring S] {n : ℕ} (f : k →+* S)
    (x : Fin n → S) (a : S) {q : MvPolynomial (Fin n) k} {d : ℕ} (hq : q.IsHomogeneous d) :
    eval₂ f (fun l => x l * a) q = a ^ d * eval₂ f x q := by
  rw [eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i, m i = d := by
    have h := hq (mem_support_iff.mp hm)
    rw [← h, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring
end GroundTheory.Heights₂.Heights.Vertical.GenSecDomain
