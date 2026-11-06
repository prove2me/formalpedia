-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.restrictedIntegralClosure_le_valuationRing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:32:02.475922+00:00
-- url     : https://prove2.me/submissions/fb96b37f-b00e-4b34-97cf-33708db7735e

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_NormalizedRestriction
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_IntegralModelCentre
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RestrictedIntegralModel

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.GlobalPlace
noncomputable section
variable {k F E : Type*} [Field k] [Finite k] [Field F] [Field E]
    [Algebra k F] [Algebra k E] [Algebra F E] [Algebra.IsAlgebraic F E]
    (Q : GlobalPlace k E)
local notation "P" => Q.restrict (F := F)
local notation "A" => GlobalPlace.valuationRing (GlobalPlace.restrict (F := F) Q)
local notation "C" => integralClosure A E
variable [Algebra (Q.restrict (F := F)).valuationRing E]
    [IsScalarTower (Q.restrict (F := F)).valuationRing F E]
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution :
    (C).toSubring ≤ Q.valuationRing.toSubring := by
  letI : IsIntegrallyClosedIn Q.valuationRing E :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn E).mp inferInstance
  change (integralClosure A E).toSubring ≤ Q.valuation.integer
  rw [Subring.integralClosure_le_iff]
  intro a
  have ha : (a : F) ∈ (Q.valuation.comap (algebraMap F E)).valuationSubring :=
    (show (P).valuationRing ≤ (Q.valuation.comap (algebraMap F E)).valuationSubring from
      le_of_eq Q.restrict_valuationRing) a.property
  change Q.valuation (algebraMap F E (a : F)) ≤ 1 at ha
  change Q.valuation (algebraMap A E a) ≤ 1
  rwa [IsScalarTower.algebraMap_apply A F E]
end QEC.Coding.AlgebraicGeometry.GlobalPlace
