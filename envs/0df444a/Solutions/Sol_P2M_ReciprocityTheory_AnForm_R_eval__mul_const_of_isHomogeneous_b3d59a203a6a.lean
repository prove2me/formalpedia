-- Prove2me | solution 1 for P2M_ReciprocityTheory_AnForm_R_eval__mul_const_of_isHomogeneous_b3d59a203a6a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:06:43.31392+00:00
-- url     : https://prove2.me/submissions/e1de8fa6-22ae-4a28-8ea5-b7ced96f76a5

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SegreIdealIsHomogeneous
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
noncomputable section
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    (g : R →+* S) (y : σ → S) (t : S) {f : MvPolynomial σ R} {n : ℕ} (hf : f.IsHomogeneous n) :
    eval₂ g (fun i => y i * t) f = eval₂ g y f * t ^ n := by
  rw [eval₂_eq, eval₂_eq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i ∈ d.support, d i = n := by
    have h := hf (mem_support_iff.1 hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h
  rw [Finset.prod_congr rfl (fun i _ => mul_pow (y i) t (d i)), Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hdeg]
  ring
end ReciprocityTheory.AnForm.R
