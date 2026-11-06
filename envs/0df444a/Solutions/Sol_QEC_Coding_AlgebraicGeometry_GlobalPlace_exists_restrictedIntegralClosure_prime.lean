-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.exists_restrictedIntegralClosure_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:33:22.720145+00:00
-- url     : https://prove2.me/submissions/cb31b164-d6f1-4b93-9138-d73a264d7c42

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_NormalizedRestriction
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_IntegralModelCentre
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RestrictedIntegralModel
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_restrictedIntegralClosure_le_valuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_exists_heightOne_order_eq
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuation_uniformizer


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
theorem _root_.solution
    [IsDedekindDomain C] [IsFractionRing C E] :
    ∃ H : IsDedekindDomain.HeightOneSpectrum C,
      H.valuationSubringAtPrime E = Q.valuationRing ∧
        (heightOnePlace (k := k) (K := E) H).order = Q.order := by
  apply Q.exists_heightOne_order_eq C
  · intro r
    exact Q.restrictedIntegralClosure_le_valuationRing r.property
  · have hu0 : (P).uniformizer ≠ 0 := by
      apply (P).valuation.ne_zero_iff.mp
      rw [(P).valuation_uniformizer]
      exact WithZero.exp_ne_zero
    have hult : (P).valuation (P).uniformizer < 1 := by
      rw [(P).valuation_uniformizer, ← WithZero.exp_zero]
      exact WithZero.exp_lt_exp.mpr (by omega)
    let u : A := ⟨(P).uniformizer, hult.le⟩
    refine ⟨algebraMap A C u, ?_, ?_⟩
    · intro hzero
      have hzero' := congrArg (algebraMap C E) hzero
      rw [map_zero, ← IsScalarTower.algebraMap_apply A C E,
        IsScalarTower.algebraMap_apply A F E] at hzero'
      apply hu0
      apply (algebraMap F E).injective
      rw [map_zero]
      exact hzero'
    · rw [← IsScalarTower.algebraMap_apply A C E, IsScalarTower.algebraMap_apply A F E]
      exact (Q.restrict_valuation_lt_one_iff (P).uniformizer).mp hult
end QEC.Coding.AlgebraicGeometry.GlobalPlace
