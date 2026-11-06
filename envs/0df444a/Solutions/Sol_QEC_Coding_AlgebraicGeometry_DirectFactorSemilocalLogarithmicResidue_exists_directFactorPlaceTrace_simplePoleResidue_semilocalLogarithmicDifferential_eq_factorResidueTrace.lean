-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalLogarithmicResidue.exists_directFactorPlaceTrace_simplePoleResidue_semilocalLogarithmicDifferential_eq_factorResidueTrace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:29:31.317872+00:00
-- url     : https://prove2.me/submissions/cab9f777-95c1-45bf-a9ad-d2e47d62725b

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalMultiplier
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorTraceResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalLogarithmicResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSemilocalLogarithmicResidue_directFactorPlace_order_semilocalMultiplier_eq_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSemilocalLogarithmicResidue_directFactorPlaceTrace_simplePoleResidue_semilocalLogarithmicDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSemilocalMultiplier_exists_directFactorSemilocalMultiplier


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalLogarithmicResidue
open scoped Polynomial RatFunc nonZeroDivisors
open UniqueFactorizationMonoid
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalLogarithmicResidue._p2m_local_instance_af27c6fddd_36
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalLogarithmicResidue._p2m_local_instance_af27c6fddd_38
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalLogarithmicResidue._p2m_local_instance_af27c6fddd_48
open DirectIntegralDifferentialResidue DirectFactorTraceResidue
namespace QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalLogarithmicResidue
theorem _root_.solution
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (b : B k F) :
    ∃ t : B k F, ∃ ht : t ≠ 0,
      GlobalPlace.order
          (AffinePlace.globalPlace k F (directFactorPlace k F p P))
          (algebraMap (B k F) F t) = 1 ∧
        directFactorPlaceTrace k F p P
            (Differential.simplePoleResidue (k := k) (F := F)
              (AffinePlace.globalPlace k F (directFactorPlace k F p P))
              (directFactorSemilocalLogarithmicDifferentialAtSimplePole
                k F p P t ht b)) =
          Ideal.Factors.factorResidueTrace p.asIdeal P b := by
  obtain ⟨t, ht, J, hspan, hcop⟩ :=
    DirectFactorSemilocalMultiplier.exists_directFactorSemilocalMultiplier
      k F p P
  exact ⟨t, ht,
    directFactorPlace_order_semilocalMultiplier_eq_one
      k F p P J hcop t ht hspan,
    directFactorPlaceTrace_simplePoleResidue_semilocalLogarithmicDifferential
      k F p P J hcop t ht b hspan⟩
end QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalLogarithmicResidue
