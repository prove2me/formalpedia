-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DirectFactorSmithTraceResidue.exists_directFactorSmith_trace_residue_compatibility
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:29:47.112533+00:00
-- url     : https://prove2.me/submissions/0706fcbb-a687-4ee1-9a61-d2ef4a04f0fb

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalCokernelTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalLogarithmicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SmithDifferentialTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSmithTraceResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSmithTraceResidue_directBaseResidueRationalAdicEquiv_quotientResidueEquiv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSmithTraceResidue_simplePoleResidue_rationalAdicSmith_eq_directFactorTrace
import Theorems.Thm_Ideal_Factors_quotientResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicPolynomialDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicSmithLogarithmicDifferential_eq_functionFieldDifferentialTrace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorResidueTransport_directFactorResidueEquiv_algebraMap
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSemilocalLogarithmicResidue_directFactorPlace_order_semilocalMultiplier_eq_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSemilocalMultiplier_exists_directFactorSemilocalMultiplier
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
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_exists_smith_bases_toMatrix_eq_diagonal_of_commute
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
    (b : B k F) :
    ∃ t : B k F, ∃ ht : t ≠ 0,
      ∃ source target : Module.Basis
        (Fin (Module.finrank (R k) (B k F))) (R k) (B k F),
      ∃ a : Fin (Module.finrank (R k) (B k F)) → R k,
      ∃ ha : ∀ i, a i ≠ 0,
        LinearMap.toMatrix source target
            (Algebra.lmul (R k) (B k F) t) = Matrix.diagonal a ∧
        GlobalPlace.order
            (AffinePlace.globalPlace k F (directFactorPlace k F p P))
            (algebraMap (B k F) F t) = 1 ∧
        ((Differential.rationalAdicSmithLogarithmicDifferentialAtSimplePole p
            source target a ha (Algebra.lmul (R k) (B k F) b) :
              Differential.simplePoleDifferentialLattice
                (GlobalPlace.rationalAdic p)) :
            Differential k (RatFunc k)) =
          FunctionFieldDifferential.functionFieldDifferentialTrace
            (k := k) (F := F)
            ((algebraMap (B k F) F b) •
              Differential.logarithmicDifferential (k := k) (F := F)
                (algebraMap (B k F) F t)) ∧
        Differential.simplePoleResidue (k := k) (F := RatFunc k)
            (GlobalPlace.rationalAdic p)
            (Differential.rationalAdicSmithLogarithmicDifferentialAtSimplePole
              p source target a ha (Algebra.lmul (R k) (B k F) b)) =
          directBaseResidueRationalAdicEquiv k p
            (directFactorPlaceTrace k F p P
              (Differential.simplePoleResidue (k := k) (F := F)
                (AffinePlace.globalPlace k F (directFactorPlace k F p P))
                (directFactorSemilocalLogarithmicDifferentialAtSimplePole
                  k F p P t ht b))) := by
  obtain ⟨t, ht, J, hspan, hcop⟩ :=
    DirectFactorSemilocalMultiplier.exists_directFactorSemilocalMultiplier
      k F p P
  let basis : Module.Basis
      (Fin (Module.finrank (R k) (B k F))) (R k) (B k F) :=
    Module.finBasis (R k) (B k F)
  have hf : Function.Injective (Algebra.lmul (R k) (B k F) t) := by
    intro x y hxy
    change t * x = t * y at hxy
    exact mul_left_cancel₀ ht hxy
  have hcomm := lmul_comp_lmul k F t b
  obtain ⟨source, target, a, ha, hdiag, _hgdiag⟩ :=
    exists_smith_bases_toMatrix_eq_diagonal_of_commute basis
      (Algebra.lmul (R k) (B k F) t)
      (Algebra.lmul (R k) (B k F) b) hf hcomm
  refine ⟨t, ht, source, target, a, ha, hdiag, ?_, ?_, ?_⟩
  · exact directFactorPlace_order_semilocalMultiplier_eq_one
      k F p P J hcop t ht hspan
  · exact
      Differential.coe_rationalAdicSmithLogarithmicDifferential_eq_functionFieldDifferentialTrace
        (k := k) (F := F) p source target a ha t b ht hdiag
  · exact simplePoleResidue_rationalAdicSmith_eq_directFactorTrace
      k F p P J hcop t ht b hspan source target a ha hdiag
end QEC.Coding.AlgebraicGeometry.DirectFactorSmithTraceResidue
