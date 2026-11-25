-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.gauss_aeval_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:26:46.41207+00:00
-- url     : https://prove2.me/submissions/7805a34d-92bc-4ebb-96e1-728aeea4e4c1

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussIndepOfLeTrdeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MvPolynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {B C : Type} [CommRing B] [CommRing C] [Algebra B C] {σ : Type}
    (g : σ → C) (P : MvPolynomial σ B) (R : Subring C)
    (hc : ∀ α, algebraMap B C (P.coeff α) ∈ R) (hg : ∀ s, g s ∈ R) : aeval g P ∈ R := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  exact R.sum_mem fun α _ => R.mul_mem (hc α) (R.prod_mem fun i _ => R.pow_mem (hg i) _)
end ReciprocityTheory.MultiplicativeHeights
