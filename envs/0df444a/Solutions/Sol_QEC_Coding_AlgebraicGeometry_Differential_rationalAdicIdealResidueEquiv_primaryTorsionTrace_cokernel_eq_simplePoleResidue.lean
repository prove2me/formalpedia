-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.rationalAdicIdealResidueEquiv_primaryTorsionTrace_cokernel_eq_simplePoleResidue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:46:33.302438+00:00
-- url     : https://prove2.me/submissions/8197fb5d-d7bf-47ba-ace2-81f138aa3254

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_SmithTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicDiagonalMatrixResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicSmithTraceResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicIdealResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicPolynomialDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_rationalAdicDiagonalLogarithmicDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicPolynomial_irreducible
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywisePolynomialDerivative_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_multiplicity_span_singleton_eq
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_cokernel_eq_sum_diagonal
attribute [local simp] QEC.Coding.AlgebraicGeometry.Differential.coe_rationalAdicPolynomialDifferential
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_add
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_one
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywisePolynomialDerivative_apply


attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicIdealResidueEquiv_mk
section
open scoped Polynomial RatFunc
namespace QEC.Coding.AlgebraicGeometry
namespace GlobalPlace
variable {k : Type*} [Field k] [Finite k]
end GlobalPlace
namespace Differential
variable {k : Type*} [Field k] [Finite k]
private theorem primaryTorsionTrace_cokernel_eq_sum_diagonal_of_eq_span
    {N : Type*} [AddCommGroup N] [Module k[X] N] [Module.Finite k[X] N]
    {n : ℕ} (source target : Module.Basis (Fin n) k[X] N)
    (a : Fin n → k[X]) (ha : ∀ i, a i ≠ 0)
    (f g : N →ₗ[k[X]] N)
    (hdiag : LinearMap.toMatrix source target f = Matrix.diagonal a)
    (hcomm : f.comp g = g.comp f)
    (P : Ideal k[X]) [P.IsMaximal]
    (q : k[X]) (hq : Irreducible q) (hP : P = Ideal.span {q})
    (depth : ℕ)
    (hdepth : ∀ i,
      multiplicity P (Ideal.span ({a i} : Set k[X])) ≤ depth) :
    primaryTorsionTrace P (cokernelEndomorphism f g hcomm) depth =
      ∑ i, (multiplicity P
          (Ideal.span ({a i} : Set k[X])) : k[X] ⧸ P) *
        Ideal.Quotient.mk P
          (LinearMap.toMatrix target target g i i) := by
  subst P
  simp_rw [multiplicity_span_singleton_eq q (a _) hq (ha _)] at hdepth ⊢
  exact primaryTorsionTrace_cokernel_eq_sum_diagonal
    source target a ha f g hdiag hcomm q hq depth hdepth
private theorem primaryTorsionTrace_cokernel_eq_sum_diagonal_at_rationalAdicIdeal
    {N : Type*} [AddCommGroup N] [Module k[X] N] [Module.Finite k[X] N]
    {n : ℕ} (source target : Module.Basis (Fin n) k[X] N)
    (a : Fin n → k[X]) (ha : ∀ i, a i ≠ 0)
    (f g : N →ₗ[k[X]] N)
    (hdiag : LinearMap.toMatrix source target f = Matrix.diagonal a)
    (hcomm : f.comp g = g.comp f)
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) (depth : ℕ)
    (hdepth : ∀ i,
      multiplicity p.asIdeal (Ideal.span ({a i} : Set k[X])) ≤ depth) :
    primaryTorsionTrace p.asIdeal (cokernelEndomorphism f g hcomm) depth =
      ∑ i, (multiplicity p.asIdeal
          (Ideal.span ({a i} : Set k[X])) : k[X] ⧸ p.asIdeal) *
        Ideal.Quotient.mk p.asIdeal
          (LinearMap.toMatrix target target g i i) := by
  exact primaryTorsionTrace_cokernel_eq_sum_diagonal_of_eq_span
    source target a ha f g hdiag hcomm p.asIdeal
      (GlobalPlace.rationalAdicPolynomial p)
      (GlobalPlace.rationalAdicPolynomial_irreducible p)
      (GlobalPlace.rationalAdic_asIdeal_eq_span p) depth hdepth
end Differential
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open scoped Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.Differential
variable {k : Type*} [Field k] [Finite k]
namespace QEC.Coding.AlgebraicGeometry.Differential
theorem _root_.solution
    {N : Type*} [AddCommGroup N] [Module k[X] N] [Module.Finite k[X] N]
    {n : ℕ} (source target : Module.Basis (Fin n) k[X] N)
    (a : Fin n → k[X]) (ha : ∀ i, a i ≠ 0)
    (f g : N →ₗ[k[X]] N)
    (hdiag : LinearMap.toMatrix source target f = Matrix.diagonal a)
    (hcomm : f.comp g = g.comp f)
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) (depth : ℕ)
    (hdepth : ∀ i,
      multiplicity p.asIdeal (Ideal.span ({a i} : Set k[X])) ≤ depth) :
    GlobalPlace.rationalAdicIdealResidueEquiv p
        (primaryTorsionTrace p.asIdeal
          (cokernelEndomorphism f g hcomm) depth) =
      simplePoleResidue (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic p)
        (rationalAdicDiagonalLogarithmicDifferentialAtSimplePole p
          (LinearMap.toMatrix target target g) a ha) := by
  rw [primaryTorsionTrace_cokernel_eq_sum_diagonal_at_rationalAdicIdeal
    source target a ha f g hdiag hcomm p depth hdepth,
    map_sum,
    simplePoleResidue_rationalAdicDiagonalLogarithmicDifferential]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, map_natCast, GlobalPlace.rationalAdicIdealResidueEquiv_mk]
  exact mul_comm _ _
end QEC.Coding.AlgebraicGeometry.Differential
