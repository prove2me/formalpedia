-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.arrayPolynomial_product_coeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:08:57.557313+00:00
-- url     : https://prove2.me/submissions/1d6ab4ac-660f-4517-af2f-6f82a408b108

import Definitions.Def_Submission_ThreeSum_TernaryExtensionDecoded
import Definitions.Def_Submission_ThreeSum_LightPolynomialProductCheck
import Definitions.Def_Submission_ThreeSum_TernaryExtensionProductSemantics
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_raw_zero
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightPolynomialCoefficient.raw_zero



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution (n m k : ℕ) (a b : ℕ → ℕ) :
    (arrayPolynomial (p := p) n a*arrayPolynomial m b).coeff k=
      (LightPolynomialCoefficient.coefficient p a b n m k : ZMod p) := by
  simp only [arrayPolynomial,Finset.sum_mul,Finset.mul_sum,finsetSum_coeff,
    monomial_mul_monomial,coeff_monomial]
  simp only [LightPolynomialCoefficient.coefficient,ZMod.natCast_mod,
    LightPolynomialCoefficient.rawCoefficient,Nat.cast_sum]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro i hi
  simp only [LightPolynomialCoefficient.term,Nat.cast_ite,Nat.cast_mul,Nat.cast_zero]
  by_cases h : i≤k ∧ k-i<m
  · rw [if_pos h]
    rw [sum_eq_single (k-i)]
    · simp [show i+(k-i)=k by omega]
    · intro j hj hne
      simp [show i+j≠k by omega]
    · intro hn
      exact False.elim (hn (mem_range.mpr h.2))
  · rw [if_neg h]
    apply sum_eq_zero
    intro j hj
    have hjm := mem_range.mp hj
    simp [show i+j≠k by omega]
end ThreeSum.TernaryExtensionEncoding
