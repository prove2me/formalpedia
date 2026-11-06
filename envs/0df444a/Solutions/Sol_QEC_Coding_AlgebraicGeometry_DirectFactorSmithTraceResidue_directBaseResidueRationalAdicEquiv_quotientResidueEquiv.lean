-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DirectFactorSmithTraceResidue.directBaseResidueRationalAdicEquiv_quotientResidueEquiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:44:46.381023+00:00
-- url     : https://prove2.me/submissions/bae8a266-9c83-4966-882b-6fc4570688f7

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalCokernelTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalLogarithmicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SmithDifferentialTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSmithTraceResidue

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
    (x : R k ⧸ p.asIdeal) :
    directBaseResidueRationalAdicEquiv k p
        (Ideal.Factors.quotientResidueEquiv p.asIdeal x) =
      GlobalPlace.rationalAdicIdealResidueEquiv p x := by
  rw [directBaseResidueRationalAdicEquiv, RingEquiv.trans_apply,
    RingEquiv.symm_apply_apply]
end QEC.Coding.AlgebraicGeometry.DirectFactorSmithTraceResidue
