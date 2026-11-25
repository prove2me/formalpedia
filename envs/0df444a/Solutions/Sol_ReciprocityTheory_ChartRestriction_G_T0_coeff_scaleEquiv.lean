-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.coeff_scaleEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:30:19.88891+00:00
-- url     : https://prove2.me/submissions/9cc2e0f5-63e1-49bc-87ee-8a44ce2f1ea1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ScaleMultiHomogeneous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BlockDegOfScale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
variable {K : Type} [Field K] {D N : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {σ : Type*} [Fintype σ] (P : σ → Prop) [DecidablePred P] (u : Kˣ)
    (F : MvPolynomial σ K) (s : σ →₀ ℕ) :
    coeff s (scaleEquiv P u F) = (u : K) ^ (∑ v ∈ Finset.univ.filter P, s v) * coeff s F := by

  have hmon : ∀ (t : σ →₀ ℕ) (a : K), scaleEquiv P u (monomial t a) =
      monomial t ((u : K) ^ (∑ v ∈ Finset.univ.filter P, t v) * a) := by
    intro t a
    have hg : ∀ v, (if P v then C (u : K) * X v else X v) ^ t v =
        C (if P v then (u : K) ^ t v else 1) * (X v : MvPolynomial σ K) ^ t v := by
      intro v
      split_ifs <;> simp [mul_pow]
    rw [scaleEquiv, AlgEquiv.ofAlgHom_apply, aeval_monomial]
    rw [monomial_eq]
    simp only [Finsupp.prod_pow, algebraMap_eq, hg, Finset.prod_mul_distrib, ← map_prod, ← Finset.prod_filter,
      Finset.prod_pow_eq_pow_sum, map_mul]
    ring
  classical
  refine MvPolynomial.induction_on' F (fun t a => ?_) (fun p q hp hq => ?_)
  · rw [hmon, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h
      rfl
    · simp
  · rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]
end ReciprocityTheory.ChartRestriction.G.T0
