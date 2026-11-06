-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DirectFactorPrimaryTrace.quotientResidueEquiv_primaryTorsionTrace_directFactorQuotientMul_eq_factorResidueTrace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:29:32.168188+00:00
-- url     : https://prove2.me/submissions/99da5946-4c16-48f8-8943-2b3654a130cc

import Mathlib.NumberTheory.FunctionField
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_IntegralTraceResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_AnnihilatedTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorPrimaryTrace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorPrimaryTrace_primaryTorsionTrace_directFactorQuotientMul_eq_quotientTrace
import Theorems.Thm_Ideal_Factors_quotientTrace_to_factorResidueTrace


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectFactorPrimaryTrace
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
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorPrimaryTrace._p2m_local_instance_a98a1bf31e_44
namespace QEC.Coding.AlgebraicGeometry.DirectFactorPrimaryTrace
theorem _root_.solution
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (b : B k F) (depth : ℕ) (hdepth : 0 < depth) :
    Ideal.Factors.quotientResidueEquiv p.asIdeal
        (primaryTorsionTrace p.asIdeal
          (Algebra.lmul (R k) (B k F ⧸ (P : Ideal (B k F)))
            (Ideal.Quotient.mk (P : Ideal (B k F)) b)) depth) =
      Ideal.Factors.factorResidueTrace p.asIdeal P b := by
  rw [primaryTorsionTrace_directFactorQuotientMul_eq_quotientTrace
    k F p P b depth hdepth]
  exact Ideal.Factors.quotientTrace_to_factorResidueTrace p.asIdeal P b
end QEC.Coding.AlgebraicGeometry.DirectFactorPrimaryTrace
