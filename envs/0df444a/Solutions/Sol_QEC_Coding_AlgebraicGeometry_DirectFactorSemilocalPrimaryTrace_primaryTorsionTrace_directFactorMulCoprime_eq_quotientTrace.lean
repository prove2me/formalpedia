-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalPrimaryTrace.primaryTorsionTrace_directFactorMulCoprime_eq_quotientTrace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:24:21.689084+00:00
-- url     : https://prove2.me/submissions/de452fb4-a1b5-4fb6-904d-fb6069e9bb6b

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorPrimaryTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CoprimeQuotientTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CRTTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalPrimaryTrace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorPrimaryTrace_primaryTorsionTrace_directFactorQuotientMul_eq_quotientTrace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_idealQuotient_eq_zero_of_isCoprime_map
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_quotientMul_eq_add


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
    primaryTorsionTrace p.asIdeal
        (Algebra.lmul (R k) (B k F ⧸ ((P : Ideal (B k F)) * J))
          (Ideal.Quotient.mk ((P : Ideal (B k F)) * J) b)) depth =
      Algebra.trace (R k ⧸ p.asIdeal)
        (B k F ⧸ (P : Ideal (B k F)))
        (Ideal.Quotient.mk (P : Ideal (B k F)) b) := by
  have hmap : Ideal.map (algebraMap (R k) (B k F)) p.asIdeal ≤
      (P : Ideal (B k F)) := by
    exact Ideal.le_of_dvd
      (dvd_of_mem_factors (Multiset.mem_toFinset.mp P.2))
  have hPJ : IsCoprime (P : Ideal (B k F)) J := by
    apply Ideal.isCoprime_iff_sup_eq.mpr
    apply top_unique
    rw [← hcop.sup_eq]
    exact sup_le_sup_right hmap J
  rw [primaryTorsionTrace_quotientMul_eq_add p.asIdeal
    (P : Ideal (B k F)) J hPJ b depth,
    primaryTorsionTrace_directFactorQuotientMul_eq_quotientTrace
      k F p P b depth hdepth,
    primaryTorsionTrace_idealQuotient_eq_zero_of_isCoprime_map
      p.asIdeal J hcop
        (Algebra.lmul (R k) (B k F ⧸ J)
          (Ideal.Quotient.mk J b)) depth,
    add_zero]
end QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalPrimaryTrace
