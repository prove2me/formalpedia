-- Prove2me | solution 1 for PermanentRollout.permanent_rollout_homogeneous_linear_slice_exists_independent_dimension_drop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/0a2979d1-4d49-4981-80ad-68c409fad59b

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_permanent_rollout_exists_linear_avoiding_minimalPrimes
import Theorems.Thm_PermanentRollout_permanent_rollout_minimalPrime_exists_variable_of_positive_dimension
import Theorems.Thm_PermanentRollout_permanent_rollout_supportDim_quotSMulTop_idealQuotient_eq_ringKrullDim_sup
import Theorems.Thm_PermanentRollout_permanent_rollout_homogeneous_linear_slice_ideal_isHomogeneous
import Theorems.Thm_PermanentRollout_permanent_rollout_homogeneous_linear_slice_ideal_snoc
import Theorems.Thm_PermanentRollout_permanent_rollout_homogeneous_linear_slice_coefficient_span_le_minimalPrime

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open Set Filter Module
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {m n : ℕ} (I : Ideal (MvPolynomial (Fin m) ℂ))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin m) ℂ))
    (c : Fin n → Fin m → ℂ)
    (hindependent : LinearIndependent ℂ c)
    (hpositive : (0 : WithBot ℕ∞) <
      ringKrullDim
        (MvPolynomial (Fin m) ℂ ⧸
          permanentRolloutHomogeneousLinearSliceIdeal I c)) :
    ∃ x : Fin m → ℂ,
      LinearIndependent ℂ (Fin.snoc c x) ∧
        ringKrullDim
          (MvPolynomial (Fin m) ℂ ⧸
            permanentRolloutHomogeneousLinearSliceIdeal I (Fin.snoc c x)) + 1 ≤
          ringKrullDim
            (MvPolynomial (Fin m) ℂ ⧸
              permanentRolloutHomogeneousLinearSliceIdeal I c) := by
  let J := permanentRolloutHomogeneousLinearSliceIdeal I c
  change (0 : WithBot ℕ∞) <
    ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) at hpositive
  have hJhomogeneous : J.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin m) ℂ) :=
    permanent_rollout_homogeneous_linear_slice_ideal_isHomogeneous I hI c
  have hcoordinate : ∀ p ∈ J.minimalPrimes,
      ∃ i : Fin m, MvPolynomial.X i ∉ p := by
    intro p hp
    exact permanent_rollout_minimalPrime_exists_variable_of_positive_dimension
      J hJhomogeneous hpositive p hp
  obtain ⟨x, hx⟩ :=
    permanent_rollout_exists_linear_avoiding_minimalPrimes J hcoordinate
  have hproper : J ≠ ⊤ := by
    intro htop
    letI : Subsingleton (MvPolynomial (Fin m) ℂ ⧸ J) :=
      Ideal.Quotient.subsingleton_iff.mpr htop
    rw [ringKrullDim_eq_bot_of_subsingleton] at hpositive
    exact (not_lt_of_ge bot_le) hpositive
  obtain ⟨⟨p, hp⟩⟩ := Ideal.nonempty_minimalPrimes hproper
  have hxspan : x ∉ Submodule.span ℂ (Set.range c) := by
    intro hspan
    apply hx p hp
    exact permanent_rollout_homogeneous_linear_slice_coefficient_span_le_minimalPrime
      I c p hp hspan
  refine ⟨x, hindependent.finSnoc hxspan, ?_⟩
  have hdrop :=
    Module.supportDim_quotSMulTop_succ_le_of_notMem_minimalPrimes
      (R := MvPolynomial (Fin m) ℂ)
      (M := MvPolynomial (Fin m) ℂ ⧸ J)
      (x := permanentRolloutLinearCoordinateCombination m x)
      (by
        intro q hq
        rw [Ideal.annihilator_quotient] at hq
        exact hx q hq)
  rw [permanent_rollout_supportDim_quotSMulTop_idealQuotient_eq_ringKrullDim_sup,
    Module.supportDim_quotient_eq_ringKrullDim] at hdrop
  rw [permanent_rollout_homogeneous_linear_slice_ideal_snoc]
  exact hdrop
end PermanentRollout
