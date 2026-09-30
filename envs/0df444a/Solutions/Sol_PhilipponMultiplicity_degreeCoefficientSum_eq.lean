-- Prove2me | solution 1 for PhilipponMultiplicity.degreeCoefficientSum_eq
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-26T02:43:27.208423+00:00
-- url     : https://prove2.me/submissions/689d46cb-6edf-42db-a412-8d81bb991751

import Theorems.Thm_PhilipponMultiplicity_multigraded_hilbert_polynomial_top_coefficients
import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert

-- Reused from Solutions/PhilipponDegreeExpansion.lean

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

private def degreeExpansionExponent {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (α : BoundedMultiIndex M) : M.FactorIndex →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (α i).val)

private theorem degree_bounded_expansion {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (F : MvPolynomial M.FactorIndex ℚ)
    (hbound : ∀ b : M.FactorIndex →₀ ℕ, (∃ i, M.ambientDimension i < b i) → coeff b F = 0) :
    F = ∑ α : BoundedMultiIndex M, monomial (degreeExpansionExponent M α)
      (coeff (degreeExpansionExponent M α) F) := by
  classical
  ext b
  rw [coeff_sum]
  by_cases hb : ∀ i, b i ≤ M.ambientDimension i
  · let α : BoundedMultiIndex M := fun i => ⟨b i, Nat.lt_succ_of_le (hb i)⟩
    have hα : degreeExpansionExponent M α = b := by ext i; rfl
    rw [Finset.sum_eq_single α]
    · simp [hα]
    · intro β _ hβα
      have hne : degreeExpansionExponent M β ≠ b := by
        intro heq
        apply hβα
        funext i
        apply Fin.ext
        exact congrArg (fun e : M.FactorIndex →₀ ℕ => e i) heq
      simp [coeff_monomial, hne]
    · simp
  · have houtside : ∃ i, M.ambientDimension i < b i := by simpa using hb
    rw [hbound b houtside]
    symm
    apply Finset.sum_eq_zero
    intro α _
    have hne : degreeExpansionExponent M α ≠ b := by
      intro heq
      obtain ⟨i, hi⟩ := houtside
      have heqi := congrArg (fun e : M.FactorIndex →₀ ℕ => e i) heq
      change (α i).val = b i at heqi
      have := (α i).isLt
      omega
    simp [coeff_monomial, hne]

theorem degreeCoefficientSum_eq {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (d : M.FactorIndex → ℕ) : idealDegreeValue M I d = degreeCoefficientSum M I d := by
  classical
  let F := Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension I
  let a := idealDimension M I
  have hbound := (multigraded_hilbert_polynomial_top_coefficients K M I hI).2
  change (eval (fun i => (d i : ℚ))) ((a.factorial : ℚ) • homogeneousComponent a F) = _
  rw [smul_eq_C_mul, map_mul, eval_C,
    degree_bounded_expansion M (homogeneousComponent a F) hbound, map_sum, Finset.mul_sum]
  unfold degreeCoefficientSum
  apply Finset.sum_congr rfl
  intro α _
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  have hsum : (degreeExpansionExponent M α).degree = ∑ i, (α i).val := by
    simp [Finsupp.degree_eq_sum, degreeExpansionExponent]
  rw [coeff_homogeneousComponent, hsum]
  change (a.factorial : ℚ) *
      ((if ∑ i, (α i).val = a then coeff (degreeExpansionExponent M α) F else 0) *
        ∏ i, (d i : ℚ) ^ (α i).val) =
    (if ∑ i, (α i).val = a then
      coeff (degreeExpansionExponent M α) F * ∏ i, ((α i).val.factorial : ℚ) else 0) *
        (a.factorial : ℚ) / (∏ i, ((α i).val.factorial : ℚ)) *
        ∏ i, (d i : ℚ) ^ (α i).val
  by_cases hα : ∑ i, (α i).val = a
  · rw [if_pos hα, if_pos hα]
    have hfac : (∏ i, ((α i).val.factorial : ℚ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ => by exact_mod_cast Nat.factorial_ne_zero _)
    field_simp
  · simp only [if_neg hα, zero_mul, mul_zero, zero_div]

end PhilipponMultiplicity

end

theorem solution {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (d : M.FactorIndex → ℕ) : idealDegreeValue M I d = degreeCoefficientSum M I d := by
  exact PhilipponMultiplicity.degreeCoefficientSum_eq M I hI d
