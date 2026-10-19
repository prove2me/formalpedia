-- Prove2me | solution 1 for PermanentRollout.homogeneousLinearSliceIdeal_exists_independent_zeroDimensional_extension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/12867a69-f4e3-4f35-a3d7-ffb217997758

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousLinearSliceIdeal_snoc
import Theorems.Thm_PermanentRollout_homogeneousLinearSliceIdeal_exists_independent_dimension_drop

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped LinearAlgebra.Projectivization
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {t p : ℕ} (I : Ideal (MvPolynomial (Fin t) ℂ))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin t) ℂ))
    (c : Fin p → Fin t → ℂ)
    (hindependent : LinearIndependent ℂ c)
    (q : ℕ) (hlength : p + q ≤ t)
    (hdimension : ringKrullDim
      (MvPolynomial (Fin t) ℂ ⧸ homogeneousLinearSliceIdeal I c) ≤
        (↑q : WithBot ℕ∞)) :
    ∃ x : Fin (p + q) → Fin t → ℂ,
      LinearIndependent ℂ x ∧
        ringKrullDim
          (MvPolynomial (Fin t) ℂ ⧸ homogeneousLinearSliceIdeal I x) ≤
          (0 : WithBot ℕ∞) := by
  induction q generalizing p c with
  | zero =>
      simpa using ⟨c, hindependent, hdimension⟩
  | succ q ih =>
      by_cases hpositive : (0 : WithBot ℕ∞) <
          ringKrullDim
            (MvPolynomial (Fin t) ℂ ⧸ homogeneousLinearSliceIdeal I c)
      · obtain ⟨a, hindependent', hdrop⟩ :=
          homogeneousLinearSliceIdeal_exists_independent_dimension_drop
            I hI c hindependent hpositive
        have hdimension' : ringKrullDim
            (MvPolynomial (Fin t) ℂ ⧸
              homogeneousLinearSliceIdeal I (Fin.snoc c a)) ≤
              (↑q : WithBot ℕ∞) := by
          apply ENat.WithBot.add_le_add_one_right_iff.mp
          calc
            ringKrullDim
                (MvPolynomial (Fin t) ℂ ⧸
                  homogeneousLinearSliceIdeal I (Fin.snoc c a)) + 1 ≤
                ringKrullDim
                  (MvPolynomial (Fin t) ℂ ⧸
                    homogeneousLinearSliceIdeal I c) := hdrop
            _ ≤ (↑(q + 1) : WithBot ℕ∞) := hdimension
            _ = (↑q : WithBot ℕ∞) + 1 := by simp
        have hlength' : (p + 1) + q ≤ t := by omega
        have hindex : (p + 1) + q = p + (q + 1) := by omega
        rw [← hindex]
        exact ih (Fin.snoc c a) hindependent' hlength' hdimension'
      · have hzero : ringKrullDim
            (MvPolynomial (Fin t) ℂ ⧸ homogeneousLinearSliceIdeal I c) ≤
              (0 : WithBot ℕ∞) := le_of_not_gt hpositive
        have hroom : p < Module.finrank ℂ (Fin t → ℂ) := by
          rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
          omega
        obtain ⟨a, hindependent'⟩ :=
          exists_linearIndependent_snoc_of_lt_finrank hindependent hroom
        have hstage : homogeneousLinearSliceIdeal I c ≤
            homogeneousLinearSliceIdeal I (Fin.snoc c a) := by
          rw [homogeneousLinearSliceIdeal_snoc]
          exact le_sup_left
        have hdimension' : ringKrullDim
            (MvPolynomial (Fin t) ℂ ⧸
              homogeneousLinearSliceIdeal I (Fin.snoc c a)) ≤
              (↑q : WithBot ℕ∞) := by
          calc
            ringKrullDim
                (MvPolynomial (Fin t) ℂ ⧸
                  homogeneousLinearSliceIdeal I (Fin.snoc c a)) ≤
                ringKrullDim
                  (MvPolynomial (Fin t) ℂ ⧸
                    homogeneousLinearSliceIdeal I c) :=
              ringKrullDim_le_of_surjective
                (Ideal.Quotient.factor hstage)
                (Ideal.Quotient.factor_surjective hstage)
            _ ≤ (0 : WithBot ℕ∞) := hzero
            _ ≤ (↑q : WithBot ℕ∞) := by exact_mod_cast Nat.zero_le q
        have hlength' : (p + 1) + q ≤ t := by omega
        have hindex : (p + 1) + q = p + (q + 1) := by omega
        rw [← hindex]
        exact ih (Fin.snoc c a) hindependent' hlength' hdimension'
end PermanentRollout
