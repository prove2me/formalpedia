-- Prove2me | solution 1 for P2M_ReciprocityTheory_AnForm_R_eval__smul_of_isHomogeneous__a2eca5c67c7e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:14:17.31282+00:00
-- url     : https://prove2.me/submissions/73a1614d-7a6c-4129-a8d5-f98650eeb788

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehom
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_LogResStC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinTypeQE
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial AlgebraicGeometry CategoryTheory
noncomputable section
variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {σ R : Type} [Fintype σ] [CommRing R] (g : ℂ →+* R)
    {f : MvPolynomial σ ℂ} {d : ℕ} (hf : f.IsHomogeneous d) (t : R) (y : σ → R) :
    eval₂ g (fun i => t * y i) f = t ^ d * eval₂ g y f := by
  classical
  rw [f.as_sum, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun mo hmo => ?_
  have hd : ∑ i, mo i = d := by
    have := hf (MvPolynomial.mem_support_iff.1 hmo)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this
  rw [MvPolynomial.eval₂_monomial, MvPolynomial.eval₂_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp_rw [mul_pow, Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum, hd]
  ring
end ReciprocityTheory.AnForm.R
