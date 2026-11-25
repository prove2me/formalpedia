-- Prove2me | solution 1 for P2M_ReciprocityTheory_AnForm_R_eval__smul_of_isMultiHomog__a1eea59a9f1b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:35:58.443331+00:00
-- url     : https://prove2.me/submissions/4ec4f358-88fc-47ea-975d-fef222406b67

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
theorem _root_.solution {R : Type} [CommRing R] (g : ℂ →+* R)
    {f : MvPolynomial (Σ k, ι k) ℂ} {a : K → ℕ} (hf : IsMultiHomog f a) (c : K → R)
    (y : (Σ k, ι k) → R) :
    eval₂ g (fun q => c q.1 * y q) f = (∏ k, c k ^ a k) * eval₂ g y f := by
  classical
  rw [f.as_sum, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun mo hmo => ?_
  rw [MvPolynomial.eval₂_monomial, MvPolynomial.eval₂_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp_rw [mul_pow, Finset.prod_mul_distrib]
  rw [Fintype.prod_sigma]
  have hk : ∀ k, ∏ i, c k ^ mo ⟨k, i⟩ = c k ^ a k := by
    intro k
    rw [Finset.prod_pow_eq_pow_sum, hf mo hmo k]
  simp only [hk]
  ring
end ReciprocityTheory.AnForm.R
