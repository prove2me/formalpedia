-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DirectSemilocalCokernelTraceSum.exists_directSemilocalUniformizer_primaryTrace_eq_sum_factorResidueTrace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:29:47.899211+00:00
-- url     : https://prove2.me/submissions/cdd748f4-6039-49ae-91f5-8931add7fcfa

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorPrimaryTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SemilocalPrincipalFactorization
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CoprimeQuotientTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CRTTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrincipalCokernelTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SemilocalCokernelTraceSum
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectSemilocalCokernelTraceSum_quotientResidueEquiv_primaryTorsionTrace_principalCokernel_eq_sum_factorResidueTrace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectSemilocalPrincipalFactorization_exists_directSemilocalUniformizerFactorization


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectSemilocalCokernelTraceSum
open scoped Polynomial RatFunc nonZeroDivisors BigOperators
open UniqueFactorizationMonoid
attribute [-instance] Ideal.Quotient.commSemiring
attribute [local instance]
  Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSemilocalCokernelTraceSum._p2m_local_instance_fa03a56197_45
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSemilocalCokernelTraceSum._p2m_local_instance_fa03a56197_50
namespace QEC.Coding.AlgebraicGeometry.DirectSemilocalCokernelTraceSum
theorem _root_.solution
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (b : B k F) (depth : ℕ) (hdepth : 0 < depth) :
    ∃ t : B k F, t ≠ 0 ∧
      (∀ P : (factors
          (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
        GlobalPlace.order
            (AffinePlace.globalPlace k F
              (DirectIntegralDifferentialResidue.directFactorPlace k F p P))
            (algebraMap (B k F) F t) = 1) ∧
      Ideal.Factors.quotientResidueEquiv p.asIdeal
          (primaryTorsionTrace p.asIdeal
            (principalCokernelMul (R := R k) t b) depth) =
        ∑ P : (factors
            (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
          Ideal.Factors.factorResidueTrace p.asIdeal P b := by
  obtain ⟨t, ht, J, hspan, hcop, horder⟩ :=
    DirectSemilocalPrincipalFactorization.exists_directSemilocalUniformizerFactorization
      k F p
  exact ⟨t, ht, horder,
    quotientResidueEquiv_primaryTorsionTrace_principalCokernel_eq_sum_factorResidueTrace
      k F p J hcop t b hspan depth hdepth⟩
end QEC.Coding.AlgebraicGeometry.DirectSemilocalCokernelTraceSum
