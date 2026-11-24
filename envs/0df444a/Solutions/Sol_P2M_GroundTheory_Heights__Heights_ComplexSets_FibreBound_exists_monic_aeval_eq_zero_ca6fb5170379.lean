-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_exists_monic_aeval_eq_zero_ca6fb5170379
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:12.21691+00:00
-- url     : https://prove2.me/submissions/713d60c1-c9b4-42e3-bdd5-ee000215bf01

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound

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
noncomputable section
variable {n d : ℕ}
open GroundTheory.Heights₂.Heights.ComplexSets.FibreBound
namespace GroundTheory.Heights₂.Heights.ComplexSets.FibreBound
theorem _root_.solution (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime]
    (A : Matrix (Fin d) (Fin n) ℂ) (hA : IsFiniteProjection J A) (s : MvPolynomial (Fin n) ℂ ⧸ J) :
    letI : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
      (projHom J A).toRingHom.toAlgebra
    ∃ g : Polynomial (MvPolynomial (Fin d) ℂ),
      g.Monic ∧ g.natDegree ≤ projDegree J A ∧ Polynomial.aeval s g = 0 := by
  let _ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    (projHom J A).toRingHom.toAlgebra
  let _ : Module (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := Algebra.toModule
  have : Module.Finite (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := hA.finite
  have : Algebra.IsIntegral (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    Algebra.IsIntegral.of_finite _ _
  obtain ⟨f, hfm, hf⟩ := Algebra.IsIntegral.isIntegral (R := MvPolynomial (Fin d) ℂ) s
  have : IsScalarTower (MvPolynomial (Fin d) ℂ) (FractionRing (MvPolynomial (Fin d) ℂ))
      (TensorProduct (MvPolynomial (Fin d) ℂ) (FractionRing (MvPolynomial (Fin d) ℂ))
        (MvPolynomial (Fin n) ℂ ⧸ J)) := TensorProduct.isScalarTower_left
  have : Module.Free (FractionRing (MvPolynomial (Fin d) ℂ))
      (TensorProduct (MvPolynomial (Fin d) ℂ) (FractionRing (MvPolynomial (Fin d) ℂ))
        (MvPolynomial (Fin n) ℂ ⧸ J)) := Module.Free.of_divisionRing _ _
  let t : TensorProduct (MvPolynomial (Fin d) ℂ) (FractionRing (MvPolynomial (Fin d) ℂ))
      (MvPolynomial (Fin n) ℂ ⧸ J) := Algebra.TensorProduct.includeRight s
  have hq : minpoly (FractionRing (MvPolynomial (Fin d) ℂ)) t ∣
      f.map (algebraMap (MvPolynomial (Fin d) ℂ) (FractionRing (MvPolynomial (Fin d) ℂ))) := by
    apply minpoly.dvd
    rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_algHom_apply, Polynomial.aeval_def, hf,
      map_zero]
  obtain ⟨g, hg⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd (FractionRing (MvPolynomial (Fin d) ℂ)) hfm hq
  have hqm : (minpoly (FractionRing (MvPolynomial (Fin d) ℂ)) t).Monic :=
    minpoly.monic (IsIntegral.of_finite _ t)
  rw [hqm.leadingCoeff, Polynomial.C_1, mul_one] at hg
  have hinj : Function.Injective
      (algebraMap (MvPolynomial (Fin d) ℂ) (FractionRing (MvPolynomial (Fin d) ℂ))) :=
    IsFractionRing.injective _ _
  refine ⟨g, Polynomial.monic_of_injective hinj (hg ▸ hqm), ?_, ?_⟩
  · rw [← Polynomial.natDegree_map_eq_of_injective hinj, hg]
    exact minpoly.natDegree_le t
  · have h1 : TensorProduct.mk (MvPolynomial (Fin d) ℂ) (FractionRing (MvPolynomial (Fin d) ℂ))
        (MvPolynomial (Fin n) ℂ ⧸ J) 1 (Polynomial.aeval s g) = 0 := by
      rw [TensorProduct.mk_apply, ← Algebra.TensorProduct.includeRight_apply,
        ← Polynomial.aeval_algHom_apply,
        ← Polynomial.aeval_map_algebraMap (FractionRing (MvPolynomial (Fin d) ℂ)), hg]
      exact minpoly.aeval _ t
    obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors (MvPolynomial (Fin d) ℂ))
      (TensorProduct.mk _ (FractionRing (MvPolynomial (Fin d) ℂ)) _ 1)).mp h1
    rw [Submonoid.smul_def, Algebra.smul_def] at hc
    refine (mul_eq_zero.mp hc).resolve_left ?_
    intro h0
    apply nonZeroDivisors.coe_ne_zero c
    apply hA.injective
    rw [map_zero]
    exact h0
end GroundTheory.Heights₂.Heights.ComplexSets.FibreBound
