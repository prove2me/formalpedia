-- Prove2me | solution 1 for PermanentRollout.homogeneousLinearSliceIdeal_exists_independent_dimension_drop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/748b9a63-2f16-4927-ad24-c5d5b7a5a48c

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_permanent_rollout_exists_linear_avoiding_minimalPrimes
import Theorems.Thm_PermanentRollout_homogeneousIdeal_minimalPrime_exists_variable_notMem
import Theorems.Thm_PermanentRollout_supportDim_quotSMulTop_idealQuotient_eq_ringKrullDim_sup
import Theorems.Thm_PermanentRollout_homogeneousLinearSliceIdeal_isHomogeneous
import Theorems.Thm_PermanentRollout_homogeneousLinearSliceIdeal_snoc
import Theorems.Thm_PermanentRollout_homogeneousLinearSliceIdeal_coefficient_span_le_minimalPrime

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped LinearAlgebra.Projectivization
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {t n : ℕ} (I : Ideal (MvPolynomial (Fin t) ℂ))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin t) ℂ))
    (c : Fin n → Fin t → ℂ)
    (hindependent : LinearIndependent ℂ c)
    (hpositive : (0 : WithBot ℕ∞) <
      ringKrullDim
        (MvPolynomial (Fin t) ℂ ⧸ homogeneousLinearSliceIdeal I c)) :
    ∃ x : Fin t → ℂ,
      LinearIndependent ℂ (Fin.snoc c x) ∧
        ringKrullDim
          (MvPolynomial (Fin t) ℂ ⧸
            homogeneousLinearSliceIdeal I (Fin.snoc c x)) + 1 ≤
          ringKrullDim
            (MvPolynomial (Fin t) ℂ ⧸
              homogeneousLinearSliceIdeal I c) := by
  let J := homogeneousLinearSliceIdeal I c
  change (0 : WithBot ℕ∞) <
    ringKrullDim (MvPolynomial (Fin t) ℂ ⧸ J) at hpositive
  have hJhomogeneous : J.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin t) ℂ) :=
    homogeneousLinearSliceIdeal_isHomogeneous I hI c
  have hcoordinate : ∀ P ∈ J.minimalPrimes,
      ∃ i : Fin t, MvPolynomial.X i ∉ P :=
    homogeneousIdeal_minimalPrime_exists_variable_notMem
      J hJhomogeneous hpositive
  obtain ⟨x, hx⟩ :=
    permanent_rollout_exists_linear_avoiding_minimalPrimes J hcoordinate
  have hproper : J ≠ ⊤ := by
    intro htop
    have hbottom : ringKrullDim (MvPolynomial (Fin t) ℂ ⧸ J) =
        (⊥ : WithBot ℕ∞) := by
      rw [htop]
      exact ringKrullDim_eq_bot_of_subsingleton
    rw [hbottom] at hpositive
    exact (not_lt_bot hpositive)
  obtain ⟨⟨P, hP⟩⟩ := Ideal.nonempty_minimalPrimes hproper
  have hxspan : x ∉ Submodule.span ℂ (Set.range c) := by
    intro hspan
    apply hx P hP
    exact homogeneousLinearSliceIdeal_coefficient_span_le_minimalPrime
      I c P hP hspan
  refine ⟨x, hindependent.finSnoc hxspan, ?_⟩
  have hdrop :=
    Module.supportDim_quotSMulTop_succ_le_of_notMem_minimalPrimes
      (R := MvPolynomial (Fin t) ℂ)
      (M := MvPolynomial (Fin t) ℂ ⧸ J)
      (x := permanentRolloutLinearCoordinateCombination t x)
      (by
        intro Q hQ
        rw [Ideal.annihilator_quotient] at hQ
        exact hx Q hQ)
  rw [supportDim_quotSMulTop_idealQuotient_eq_ringKrullDim_sup,
    Module.supportDim_quotient_eq_ringKrullDim] at hdrop
  rw [homogeneousLinearSliceIdeal_snoc]
  exact hdrop
end PermanentRollout
