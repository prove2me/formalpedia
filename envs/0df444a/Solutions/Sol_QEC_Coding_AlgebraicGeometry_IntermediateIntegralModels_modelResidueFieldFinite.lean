-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels.modelResidueFieldFinite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:32:09.711203+00:00
-- url     : https://prove2.me/submissions/9b3c2320-8cc6-4385-85c8-db0256250f17

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneQuotientResidue
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_IntermediateIntegralModels

set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
variable (A F E : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Field E] [Algebra A F] [IsFractionRing A F]
    [Algebra F E] [Algebra A E] [IsScalarTower A F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
local notation "C" => Model A F E
variable [IsDedekindDomain (integralClosure A E)] [Module.Finite A (integralClosure A E)]
omit [IsDedekindDomain (integralClosure A E)] [Module.Finite A (integralClosure A E)]
namespace QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels
theorem _root_.solution
    {k : Type*} [Field k] [Finite k]
    [Algebra k F] [Algebra k E] [IsScalarTower k F E]
    [Finite (IsLocalRing.ResidueField A)]
    (K : IntermediateField F E) (H : IsDedekindDomain.HeightOneSpectrum (C K)) :
    Finite (heightOnePlace (k := k) (K := K) H).residueField := by
  let m := IsLocalRing.maximalIdeal A
  let I := H.asIdeal
  let P := H.under A
  have hPm : P.asIdeal = m :=
    IsLocalRing.eq_maximalIdeal (P.isPrime.isMaximal P.ne_bot)
  letI : I.LiesOver m := by
    rw [← hPm]
    exact ⟨rfl⟩
  let quotientAlgebra : Algebra (A ⧸ m) ((C K) ⧸ I) :=
    Ideal.Quotient.algebraQuotientOfLEComap (Ideal.over_def I m).le
  letI : Algebra (A ⧸ m) ((C K) ⧸ I) := quotientAlgebra
  letI : Module.Finite (A ⧸ m) ((C K) ⧸ I) :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ m) ((C K) ⧸ I)
  letI : Finite (A ⧸ m) := inferInstanceAs (Finite (IsLocalRing.ResidueField A))
  letI : Finite ((C K) ⧸ I) := Module.finite_of_finite (A ⧸ m)
  let e : ((C K) ⧸ I) ≃+* (heightOnePlace (k := k) (K := K) H).residueField :=
    H.quotientResidueEquivValuation (K := K)
  exact Finite.of_equiv ((C K) ⧸ I) e.toEquiv
end QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels
