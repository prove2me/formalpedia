-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalPrimaryTrace.quotientResidueEquiv_primaryTorsionTrace_directFactorMulCoprime_eq_factorResidueTrace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:29:35.763855+00:00
-- url     : https://prove2.me/submissions/781b4cde-a982-46c8-a5c5-923ee86e082d

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorPrimaryTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CoprimeQuotientTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CRTTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalPrimaryTrace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSemilocalPrimaryTrace_primaryTorsionTrace_directFactorMulCoprime_eq_quotientTrace
import Theorems.Thm_Ideal_Factors_quotientTrace_to_factorResidueTrace


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalPrimaryTrace
open scoped Polynomial RatFunc nonZeroDivisors
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
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalPrimaryTrace._p2m_local_instance_de14ef7384_45
open DirectFactorPrimaryTrace
namespace QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalPrimaryTrace
theorem _root_.solution
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (J : Ideal (B k F))
    (hcop : IsCoprime
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal) J)
    (b : B k F) (depth : ℕ) (hdepth : 0 < depth) :
    Ideal.Factors.quotientResidueEquiv p.asIdeal
        (primaryTorsionTrace p.asIdeal
          (Algebra.lmul (R k) (B k F ⧸ ((P : Ideal (B k F)) * J))
            (Ideal.Quotient.mk ((P : Ideal (B k F)) * J) b)) depth) =
      Ideal.Factors.factorResidueTrace p.asIdeal P b := by
  rw [primaryTorsionTrace_directFactorMulCoprime_eq_quotientTrace
    k F p P J hcop b depth hdepth]
  exact Ideal.Factors.quotientTrace_to_factorResidueTrace p.asIdeal P b
end QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalPrimaryTrace
