-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.polyInner_eq_inner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:05:54.373247+00:00
-- url     : https://prove2.me/submissions/cc1415d5-355a-41e1-9b41-d4c5f8a005eb

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExpTorusMeanLeL2OfLex
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_coeffVec_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Finset
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {ι : Type*} (T : Finset (ι →₀ ℕ)) (P Q : MvPolynomial ι ℂ)
    (hP : P.support ⊆ T) : polyInner P Q = inner ℂ (coeffVec T Q) (coeffVec T P) := by
  classical
  rw [PiLp.inner_apply]
  simp only [coeffVec_apply, RCLike.inner_apply, polyInner]
  rw [Finset.sum_coe_sort T (fun t => P.coeff t * (starRingEnd ℂ) (Q.coeff t))]
  exact Finset.sum_subset hP (fun t _ ht => by rw [MvPolynomial.notMem_support_iff.mp ht, zero_mul])
end ReciprocityTheory.MultiplicativeHeights
