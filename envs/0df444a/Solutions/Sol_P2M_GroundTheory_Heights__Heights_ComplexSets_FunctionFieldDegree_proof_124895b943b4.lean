-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_FunctionFieldDegree_proof_124895b943b4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:13.011248+00:00
-- url     : https://prove2.me/submissions/7361b87b-ed08-478c-928f-2ccd63f3ae0c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFunctionFieldDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFunctionFieldDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial
open scoped nonZeroDivisors
noncomputable section
set_option synthInstance.maxHeartbeats 400000
namespace GroundTheory.Heights₂.Heights.ComplexSets
namespace FunctionFieldDegree
theorem _root_.solution : FunctionFieldDegree.Statement := by
  intro n d J A hJ hA
  let := projAlgebra J A
  let : Module (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := Algebra.toModule
  intro K L _ _ _ _ _ _ _ _ _ _
  have := hJ
  have : Module.Finite (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := hA.finite
  have : FaithfulSMul (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (by exact hA.injective)
  have : Algebra.IsAlgebraic (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    Algebra.IsIntegral.isAlgebraic

  have hbc : IsBaseChange K (IsScalarTower.toAlgHom (MvPolynomial (Fin d) ℂ)
      (MvPolynomial (Fin n) ℂ ⧸ J) L).toLinearMap :=
    IsLocalizedModule.isBaseChange (MvPolynomial (Fin d) ℂ)⁰ K _
  have hfin : FiniteDimensional K L := Module.Finite.equiv hbc.equiv
  refine ⟨hfin, ?_, ?_⟩
  ·
    rw [← hbc.equiv.finrank_eq, projDegree]
    let e : FractionRing (MvPolynomial (Fin d) ℂ) ≃ₐ[MvPolynomial (Fin d) ℂ] K :=
      FractionRing.algEquiv (MvPolynomial (Fin d) ℂ) K
    symm
    refine Algebra.finrank_eq_of_equiv_equiv e.toRingEquiv
      (Algebra.TensorProduct.congr e AlgEquiv.refl).toRingEquiv ?_
    ext x
    simp [Algebra.TensorProduct.algebraMap_apply]
  ·
    rw [eq_top_iff]
    intro z _
    set F := IntermediateField.adjoin K (Set.range fun j =>
      algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) L (Ideal.Quotient.mk J (X j)))
    have hB : ∀ p : MvPolynomial (Fin n) ℂ,
        algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) L (Ideal.Quotient.mk J p) ∈ F := by
      intro p
      induction p using MvPolynomial.induction_on with
      | C a =>
        have hC : Ideal.Quotient.mk J (C a) =
            algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) (C a) := by
          change _ = Ideal.Quotient.mk J (pullback A (C a))
          have h := (pullback A).commutes a
          simp only [MvPolynomial.algebraMap_eq] at h
          rw [h]
        rw [hC, ← IsScalarTower.algebraMap_apply,
          IsScalarTower.algebraMap_apply (MvPolynomial (Fin d) ℂ) K L]
        exact F.algebraMap_mem _
      | add p q hp hq => rw [map_add, map_add]; exact F.add_mem hp hq
      | mul_X p j hp =>
        rw [map_mul, map_mul]
        exact F.mul_mem hp (IntermediateField.subset_adjoin _ _ ⟨j, rfl⟩)
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Fin n) ℂ ⧸ J) z
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact F.div_mem (hB p) (hB q)
end FunctionFieldDegree
end GroundTheory.Heights₂.Heights.ComplexSets
