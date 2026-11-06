-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalCokernelTrace.exists_primaryTorsionTrace_principalCokernel_eq_quotientTrace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:29:37.394674+00:00
-- url     : https://prove2.me/submissions/490ebfd8-6e39-439a-bcae-0af5d1983723

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalPrimaryTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalMultiplier
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrincipalCokernelTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalCokernelTrace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSemilocalCokernelTrace_primaryTorsionTrace_principalCokernel_eq_quotientTrace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSemilocalMultiplier_exists_directFactorSemilocalMultiplier


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
    (b : B k F) (depth : ℕ) (hdepth : 0 < depth) :
    ∃ t : B k F, t ≠ 0 ∧
      primaryTorsionTrace p.asIdeal
          (principalCokernelMul (R := R k) t b) depth =
        Algebra.trace (R k ⧸ p.asIdeal)
          (B k F ⧸ (P : Ideal (B k F)))
          (Ideal.Quotient.mk (P : Ideal (B k F)) b) := by
  obtain ⟨t, ht, J, hspan, hcop⟩ :=
    DirectFactorSemilocalMultiplier.exists_directFactorSemilocalMultiplier
      k F p P
  exact ⟨t, ht,
    primaryTorsionTrace_principalCokernel_eq_quotientTrace
      k F p P J hcop t b hspan depth hdepth⟩
end QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalCokernelTrace
