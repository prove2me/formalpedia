-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DirectFactorTraceResidue.directIntegralTrace_residue_eq_sum_directFactorTraces
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:29:28.965351+00:00
-- url     : https://prove2.me/submissions/e9661eae-1bb8-4fe8-9bf1-eebc7ed55cfd

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorResidueTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorTraceResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorTraceResidue_directFactorPlaceTrace_simplePoleResidue_directIntegralLogarithmicDifferential
import Theorems.Thm_Ideal_Factors_integralTrace_residue_eq_sum_ramificationIdx_mul


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectFactorTraceResidue
open scoped Polynomial RatFunc nonZeroDivisors
open UniqueFactorizationMonoid
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorTraceResidue.directFactorTraceResidue_constantAlgebra
attribute [local instance] directFactorTraceResidue_constantAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorTraceResidue._p2m_local_instance_49470eb06b_39
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorTraceResidue._p2m_local_instance_49470eb06b_49
open DirectIntegralDifferentialResidue DirectFactorResidueTransport
namespace QEC.Coding.AlgebraicGeometry.DirectFactorTraceResidue
theorem _root_.solution
    (p : IsDedekindDomain.HeightOneSpectrum (R k)) (b : B k F) :
    algebraMap (R k) p.asIdeal.ResidueField
        (Algebra.intTrace (R k) (B k F) b) =
      ∑ P : (factors
          (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
        directFactorPlaceTrace k F p P
          (Differential.simplePoleResidue (k := k) (F := F)
            (AffinePlace.globalPlace k F (directFactorPlace k F p P))
            (directIntegralLogarithmicDifferentialAtSimplePole k F p P b)) := by
  have hpmap : Ideal.map (algebraMap (R k) (B k F)) p.asIdeal ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot p.ne_bot
  rw [Ideal.Factors.integralTrace_residue_eq_sum_ramificationIdx_mul
    p.asIdeal hpmap b]
  apply Finset.sum_congr rfl
  intro P _
  rw [directFactorPlaceTrace_simplePoleResidue_directIntegralLogarithmicDifferential]
end QEC.Coding.AlgebraicGeometry.DirectFactorTraceResidue
