-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.scaleEquiv_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:51:52.89645+00:00
-- url     : https://prove2.me/submissions/99953776-ff79-4481-b31d-88cc4de1f511

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ScaleMultiHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
section Scale
variable {S σ : Type*} [CommRing S]
private theorem scaleEquiv_apply' (P : σ → Prop) [DecidablePred P] (u : Sˣ)
    (p : MvPolynomial σ S) :
    scaleEquiv P u p = aeval (fun v => if P v then C (u : S) * X v else X v) p := rfl
end Scale
section Blocks
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}
end Blocks
section Norm
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}
end Norm
namespace Data
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (NumberField.RingOfIntegers K) (A c)]
variable (d : Data K ι Ω WT A)
end Data
end ReciprocityTheory.ChartRestriction.G.T0
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
variable {S σ : Type*} [CommRing S]
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution [Fintype σ] (P : σ → Prop) [DecidablePred P] (u : Sˣ)
    (s : σ →₀ ℕ) (a : S) :
    scaleEquiv P u (monomial s a) =
      C ((u : S) ^ (∑ v ∈ Finset.univ.filter P, s v)) * monomial s a := by
  have hf : ∀ v : σ, (if P v then C (u : S) * X v else X v) ^ (s v) =
      C (if P v then (u : S) ^ (s v) else 1) * X v ^ (s v) := by
    intro v
    by_cases hv : P v
    · rw [if_pos hv, if_pos hv, mul_pow, MvPolynomial.C_pow]
    · rw [if_neg hv, if_neg hv, MvPolynomial.C_1, one_mul]
  have hc : C ((u : S) ^ (∑ v ∈ Finset.univ.filter P, s v)) =
      ∏ v, (C (if P v then (u : S) ^ (s v) else 1) : MvPolynomial σ S) := by
    rw [← Finset.prod_pow_eq_pow_sum, Finset.prod_filter, map_prod]
  rw [scaleEquiv_apply', MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq,
    Finsupp.prod_fintype s (fun v k => (if P v then C (u : S) * X v else X v) ^ k)
      (fun v => pow_zero _),
    Finsupp.prod_fintype s (fun v k => (X v : MvPolynomial σ S) ^ k) (fun v => pow_zero _), hc]
  simp only [hf, Finset.prod_mul_distrib, MvPolynomial.algebraMap_eq]
  ring
end ReciprocityTheory.ChartRestriction.G.T0
