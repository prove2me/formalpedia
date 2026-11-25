-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.segreMap_aeval_update
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:19:06.899775+00:00
-- url     : https://prove2.me/submissions/5c1f778b-ecdb-4c13-97ac-f868c89b3708

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SegreIdealIsHomogeneous
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA
import Theorems.Thm_ReciprocityTheory_AnForm_R_prod_update_eq
import Theorems.Thm_ReciprocityTheory_AnForm_R_segreMap_X

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
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution [DecidableEq K] (p : (k : K) → ι k) {f : MvPolynomial (Σ k, ι k) ℂ}
    {a : K → ℕ} (hf : IsMultiHomog f a) :
    segreMap (aeval (fun q : Σ k, ι k => (X (Function.update p q.1 q.2) :
        MvPolynomial ((k : K) → ι k) ℂ)) f) =
      (∏ k, (∏ j ∈ Finset.univ.erase k, (X ⟨j, p j⟩ : MvPolynomial (Σ k, ι k) ℂ)) ^ a k) * f := by
  have h1 : segreMap (aeval (fun q : Σ k, ι k => (X (Function.update p q.1 q.2) :
        MvPolynomial ((k : K) → ι k) ℂ)) f) =
      aeval (fun q : Σ k, ι k => segreMap (X (Function.update p q.1 q.2) :
        MvPolynomial ((k : K) → ι k) ℂ)) f := by
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  have hY : (fun q : Σ k, ι k => segreMap (X (Function.update p q.1 q.2) :
        MvPolynomial ((k : K) → ι k) ℂ)) =
      fun q => X q * ∏ j ∈ Finset.univ.erase q.1, (X ⟨j, p j⟩ : MvPolynomial (Σ k, ι k) ℂ) := by
    funext q
    rw [segreMap_X, prod_update_eq X p q.1 q.2]
  rw [h1, hY]
  have key : ∀ m ∈ f.support,
      aeval (fun q : Σ k, ι k => X q *
          ∏ j ∈ Finset.univ.erase q.1, (X ⟨j, p j⟩ : MvPolynomial (Σ k, ι k) ℂ))
        (monomial m (f.coeff m)) =
      (∏ k, (∏ j ∈ Finset.univ.erase k, (X ⟨j, p j⟩ : MvPolynomial (Σ k, ι k) ℂ)) ^ a k) *
        monomial m (f.coeff m) := by
    intro m hm
    have hdeg := hf m hm
    rw [aeval_monomial, monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _), MvPolynomial.algebraMap_eq]
    simp_rw [mul_pow]
    rw [Finset.prod_mul_distrib]
    have hc : ∏ q : (Σ k, ι k),
        (∏ j ∈ Finset.univ.erase q.1, (X ⟨j, p j⟩ : MvPolynomial (Σ k, ι k) ℂ)) ^ m q =
        ∏ k, (∏ j ∈ Finset.univ.erase k, (X ⟨j, p j⟩ : MvPolynomial (Σ k, ι k) ℂ)) ^ a k := by
      rw [Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun k _ => ?_
      dsimp only
      rw [Finset.prod_pow_eq_pow_sum, hdeg k]
    rw [hc]
    ring
  conv_lhs => rw [f.as_sum]
  rw [map_sum]
  conv_rhs => rw [f.as_sum]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl key
end ReciprocityTheory.AnForm.R
