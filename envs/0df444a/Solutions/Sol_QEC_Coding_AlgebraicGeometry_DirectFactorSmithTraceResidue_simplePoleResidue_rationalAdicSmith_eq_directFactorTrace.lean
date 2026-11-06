-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DirectFactorSmithTraceResidue.simplePoleResidue_rationalAdicSmith_eq_directFactorTrace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:49:57.788295+00:00
-- url     : https://prove2.me/submissions/f5d41e78-a6b3-47f2-9bfc-1eb7c9e4be52

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalCokernelTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalLogarithmicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SmithDifferentialTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSmithTraceResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSmithTraceResidue_directBaseResidueRationalAdicEquiv_quotientResidueEquiv
import Theorems.Thm_Ideal_Factors_quotientResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicPolynomialDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_rationalAdicSmithLogarithmicDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorResidueTransport_directFactorResidueEquiv_algebraMap
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSemilocalCokernelTrace_quotientResidueEquiv_primaryTorsionTrace_principalCokernel_eq_factorResidueTrace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSemilocalLogarithmicResidue_directFactorPlaceTrace_simplePoleResidue_semilocalLogarithmicDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicIdealResidueEquiv_mk
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
attribute [local simp] Ideal.Factors.quotientResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.Differential.coe_rationalAdicPolynomialDifferential
attribute [local simp] QEC.Coding.AlgebraicGeometry.DirectFactorResidueTransport.directFactorResidueEquiv_algebraMap
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicIdealResidueEquiv_mk
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


attribute [local simp] QEC.Coding.AlgebraicGeometry.DirectFactorSmithTraceResidue.directBaseResidueRationalAdicEquiv_quotientResidueEquiv
section
namespace QEC.Coding.AlgebraicGeometry.DirectFactorSmithTraceResidue
open scoped Polynomial RatFunc nonZeroDivisors
open UniqueFactorizationMonoid
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
open DirectIntegralDifferentialResidue DirectFactorTraceResidue
open DirectFactorSemilocalLogarithmicResidue
private theorem lmul_comp_lmul (t b : B k F) :
    (Algebra.lmul (R k) (B k F) t).comp
        (Algebra.lmul (R k) (B k F) b) =
      (Algebra.lmul (R k) (B k F) b).comp
        (Algebra.lmul (R k) (B k F) t) := by
  apply LinearMap.ext
  intro x
  change t * (b * x) = b * (t * x)
  ring
end QEC.Coding.AlgebraicGeometry.DirectFactorSmithTraceResidue
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectFactorSmithTraceResidue
open scoped Polynomial RatFunc nonZeroDivisors
open UniqueFactorizationMonoid
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorSmithTraceResidue._p2m_local_instance_176fcc4610_37
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorSmithTraceResidue._p2m_local_instance_176fcc4610_39
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorSmithTraceResidue._p2m_local_instance_176fcc4610_49
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorSmithTraceResidue._p2m_local_instance_176fcc4610_53
open DirectIntegralDifferentialResidue DirectFactorTraceResidue
open DirectFactorSemilocalLogarithmicResidue
namespace QEC.Coding.AlgebraicGeometry.DirectFactorSmithTraceResidue
theorem _root_.solution
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (J : Ideal (B k F))
    (hcop : IsCoprime
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal) J)
    (t : B k F) (ht : t ≠ 0) (b : B k F)
    (hspan : Ideal.span ({t} : Set (B k F)) =
      (P : Ideal (B k F)) * J)
    {n : ℕ}
    (source target : Module.Basis (Fin n) (R k) (B k F))
    (a : Fin n → R k) (ha : ∀ i, a i ≠ 0)
    (hdiag : LinearMap.toMatrix source target
      (Algebra.lmul (R k) (B k F) t) = Matrix.diagonal a) :
    Differential.simplePoleResidue (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic p)
        (Differential.rationalAdicSmithLogarithmicDifferentialAtSimplePole p
          source target a ha (Algebra.lmul (R k) (B k F) b)) =
      directBaseResidueRationalAdicEquiv k p
        (directFactorPlaceTrace k F p P
          (Differential.simplePoleResidue (k := k) (F := F)
            (AffinePlace.globalPlace k F (directFactorPlace k F p P))
            (directFactorSemilocalLogarithmicDifferentialAtSimplePole
              k F p P t ht b))) := by
  let depth : ℕ :=
    (∑ i, multiplicity p.asIdeal
      (Ideal.span ({a i} : Set (R k)))).succ
  have hdepth : ∀ i, multiplicity p.asIdeal
      (Ideal.span ({a i} : Set (R k))) ≤ depth := by
    intro i
    apply le_trans ?_ (Nat.le_succ _)
    exact Finset.single_le_sum
      (fun j _ => Nat.zero_le
        (multiplicity p.asIdeal (Ideal.span ({a j} : Set (R k)))))
      (Finset.mem_univ i)
  have hcomm := lmul_comp_lmul k F t b
  have hcokernel :
      cokernelEndomorphism
          (Algebra.lmul (R k) (B k F) t)
          (Algebra.lmul (R k) (B k F) b) hcomm =
        principalCokernelMul (R := R k) t b := by
    rfl
  have hrational :=
    Differential.simplePoleResidue_rationalAdicSmithLogarithmicDifferential
      p source target a ha
        (Algebra.lmul (R k) (B k F) t)
        (Algebra.lmul (R k) (B k F) b)
        hdiag hcomm depth hdepth
  have hprimary :=
    DirectFactorSemilocalCokernelTrace.quotientResidueEquiv_primaryTorsionTrace_principalCokernel_eq_factorResidueTrace
      k F p P J hcop t b hspan depth (Nat.succ_pos _)
  have hupper :=
    directFactorPlaceTrace_simplePoleResidue_semilocalLogarithmicDifferential
      k F p P J hcop t ht b hspan
  calc
    Differential.simplePoleResidue (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic p)
        (Differential.rationalAdicSmithLogarithmicDifferentialAtSimplePole p
          source target a ha (Algebra.lmul (R k) (B k F) b)) =
      GlobalPlace.rationalAdicIdealResidueEquiv p
        (primaryTorsionTrace p.asIdeal
          (cokernelEndomorphism
            (Algebra.lmul (R k) (B k F) t)
            (Algebra.lmul (R k) (B k F) b) hcomm) depth) := hrational
    _ = directBaseResidueRationalAdicEquiv k p
        (Ideal.Factors.quotientResidueEquiv p.asIdeal
          (primaryTorsionTrace p.asIdeal
            (principalCokernelMul (R := R k) t b) depth)) := by
      rw [hcokernel,
        directBaseResidueRationalAdicEquiv_quotientResidueEquiv]
    _ = directBaseResidueRationalAdicEquiv k p
        (Ideal.Factors.factorResidueTrace p.asIdeal P b) := by
      rw [hprimary]
    _ = directBaseResidueRationalAdicEquiv k p
        (directFactorPlaceTrace k F p P
          (Differential.simplePoleResidue (k := k) (F := F)
            (AffinePlace.globalPlace k F (directFactorPlace k F p P))
            (directFactorSemilocalLogarithmicDifferentialAtSimplePole
              k F p P t ht b))) := by
      rw [hupper]
end QEC.Coding.AlgebraicGeometry.DirectFactorSmithTraceResidue
