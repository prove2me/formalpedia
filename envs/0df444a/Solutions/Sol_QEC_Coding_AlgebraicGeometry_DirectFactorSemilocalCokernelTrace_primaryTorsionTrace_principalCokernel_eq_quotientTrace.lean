-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalCokernelTrace.primaryTorsionTrace_principalCokernel_eq_quotientTrace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:29:02.938785+00:00
-- url     : https://prove2.me/submissions/ad435320-ba10-4ece-8cc0-c7bc62030b97

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalPrimaryTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalMultiplier
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrincipalCokernelTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalCokernelTrace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSemilocalPrimaryTrace_primaryTorsionTrace_directFactorMulCoprime_eq_quotientTrace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_cokernel_lmul_eq_idealQuotientMul_of_eq


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalCokernelTrace
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
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalCokernelTrace._p2m_local_instance_d1e0a01c5a_46
namespace QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalCokernelTrace
theorem _root_.solution
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (J : Ideal (B k F))
    (hcop : IsCoprime
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal) J)
    (t b : B k F)
    (hspan : Ideal.span ({t} : Set (B k F)) =
      (P : Ideal (B k F)) * J)
    (depth : ℕ) (hdepth : 0 < depth) :
    primaryTorsionTrace p.asIdeal
        (principalCokernelMul (R := R k) t b) depth =
      Algebra.trace (R k ⧸ p.asIdeal)
        (B k F ⧸ (P : Ideal (B k F)))
        (Ideal.Quotient.mk (P : Ideal (B k F)) b) := by
  calc
    primaryTorsionTrace p.asIdeal
        (principalCokernelMul (R := R k) t b) depth =
      primaryTorsionTrace p.asIdeal
        (Algebra.lmul (R k) (B k F ⧸ ((P : Ideal (B k F)) * J))
          (Ideal.Quotient.mk ((P : Ideal (B k F)) * J) b)) depth :=
      primaryTorsionTrace_cokernel_lmul_eq_idealQuotientMul_of_eq
        p.asIdeal t b ((P : Ideal (B k F)) * J) hspan depth
    _ = _ :=
      DirectFactorSemilocalPrimaryTrace.primaryTorsionTrace_directFactorMulCoprime_eq_quotientTrace
        k F p P J hcop b depth hdepth
end QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalCokernelTrace
