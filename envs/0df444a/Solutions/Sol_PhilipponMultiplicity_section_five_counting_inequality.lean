-- Prove2me | solution 1 for PhilipponMultiplicity.section_five_counting_inequality
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-28T19:32:22.451415+00:00
-- url     : https://prove2.me/submissions/962d8081-639d-4a1c-b4d3-ebf7c50b6301

import Theorems.Thm_PhilipponMultiplicity_section_five_contact_cosets
import Theorems.Thm_PhilipponMultiplicity_section_five_contact_coset_multiplicity
import Theorems.Thm_PhilipponMultiplicity_section_five_finite_coset_degree_bound
import Theorems.Thm_PhilipponMultiplicity_multigraded_hilbert_polynomial_top_coefficients

section
-- Implementation: Solutions/PhilipponCountingReductionSupport.lean

set_option autoImplicit false
set_option maxHeartbeats 400000
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity

theorem counting_vanishingIdeal_homogeneous {K : Type*} [Field K]
    (M : MultiProjectiveSpace K) (S : Set M.Point) :
    IsMultihomogeneousIdeal M (M.vanishingIdeal S) := by
  classical
  let w := Hilbert.blockWeight M.factorCount M.ambientDimension
  have hw (e : M.Variable →₀ ℕ) (i : M.FactorIndex) :
      Finsupp.weight w e i = ∑ j, e ⟨i,j⟩ := by
    rw [Finsupp.weight_eq_sum,Fintype.sum_sigma]
    change (∑ b : M.FactorIndex, ∑ j : Fin (M.ambientDimension b + 1),
      e ⟨b,j⟩ • w ⟨b,j⟩) i = _
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,w,Hilbert.blockWeight,
      Pi.single_apply,mul_ite,mul_one,mul_zero]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hbi
      simp [Ne.symm hbi]
    · simp
  letI := MvPolynomial.weightedGradedAlgebra K w
  have hh : (M.vanishingIdeal S).IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    apply Ideal.homogeneous_span
    intro P hP
    obtain ⟨D,hD⟩ := hP.1
    refine ⟨D,?_⟩
    intro e he
    funext i
    rw [hw]
    exact hD e (mem_support_iff.mpr he) i
  intro P hP d
  exact weightedHomogeneousComponent_mem_of_mem K w hh hP d

theorem hilbertDegreeForm_nonneg {K : Type*} [Field K]
    (G : EmbeddedGroupProduct K) (V : Set G.Point) (D : G.FactorIndex → ℕ) :
    0 ≤ hilbertDegreeForm G V D := by
  classical
  have htop := (multigraded_hilbert_polynomial_top_coefficients K G.ambient
    (G.vanishingIdeal V) (counting_vanishingIdeal_homogeneous G.ambient (G.embedding '' V))).1
  have hn : 0 ≤ Hilbert.degreeValue K G.factorCount G.ambient.ambientDimension
      (G.vanishingIdeal V) D := by
    unfold Hilbert.degreeValue Hilbert.degreeForm
    rw [MvPolynomial.smul_eq_C_mul,map_mul,MvPolynomial.eval_C]
    apply mul_nonneg (Nat.cast_nonneg _)
    rw [MvPolynomial.eval_eq]
    exact Finset.sum_nonneg fun e _ => mul_nonneg (htop e)
      (Finset.prod_nonneg fun i _ => pow_nonneg (Nat.cast_nonneg _) _)
  change (0 : ℝ) ≤ (Hilbert.degreeValue K G.factorCount G.ambient.ambientDimension
    (G.vanishingIdeal V) D : ℝ)
  exact_mod_cast hn

end PhilipponMultiplicity

end
end

open PhilipponMultiplicity
open scoped BigOperators

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G)
    (C : SectionFiveConstruction G A) :
    let H := C.stabilizer.identityComponent
      let s := analyticCodimension A H
      (Nat.choose (C.contactParameter + s) s : ℝ) *
          (cosetCount C.samplingSet H : ℝ) * hilbertDegreeForm G H C.degrees ≤
        hilbertDegreeForm G Set.univ C.scaledDegrees := by
  obtain ⟨H,hH,hconn,R,hR,hcover,hdisjoint,hcount⟩ := section_five_contact_cosets K hK G A C
  have hmult := fun g hg => section_five_contact_coset_multiplicity K hK G A C H hH hconn g (hR g hg)
  have hdegree := section_five_finite_coset_degree_bound K hK G A C H hH hconn R
    (Nat.choose (C.contactParameter + analyticCodimension A H.carrier)
      (analyticCodimension A H.carrier)) hdisjoint hmult
  dsimp only
  rw [← hH]
  apply le_trans ?_ hdegree
  apply mul_le_mul_of_nonneg_right ?_ (hilbertDegreeForm_nonneg G H.carrier C.degrees)
  apply mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  exact_mod_cast hcount
