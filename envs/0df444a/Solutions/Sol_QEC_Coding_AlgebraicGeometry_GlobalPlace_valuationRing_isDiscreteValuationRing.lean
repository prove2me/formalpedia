-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.valuationRing_isDiscreteValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:15:39.161668+00:00
-- url     : https://prove2.me/submissions/9fa53c90-4572-4980-b20b-18c319c6b19a

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_Differential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlace
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuation_uniformizer

section
namespace QEC.Coding.AlgebraicGeometry
open scoped WithZero
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
namespace Differential
end Differential
namespace GlobalPlace
private theorem valuation_isNontrivial (P : GlobalPlace k F) :
    P.valuation.IsNontrivial := by
  rw [Valuation.isNontrivial_iff_exists_lt_one]
  refine ⟨P.uniformizer, ?_, ?_⟩
  · apply P.valuation.ne_zero_iff.mp
    rw [P.valuation_uniformizer]
    exact WithZero.exp_ne_zero
  · rw [P.valuation_uniformizer, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
end GlobalPlace
namespace Differential
end Differential
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped WithZero
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
open QEC.Coding.AlgebraicGeometry.GlobalPlace
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution (P : GlobalPlace k F) :
    IsDiscreteValuationRing P.valuationRing := by
  letI : P.valuation.IsNontrivial := valuation_isNontrivial P
  letI : IsCyclic (MonoidWithZeroHom.valueGroup (.ofClass P.valuation)) := inferInstance
  letI : Nontrivial (MonoidWithZeroHom.valueGroup (.ofClass P.valuation)) := inferInstance
  exact Valuation.valuationSubring_isDiscreteValuationRing P.valuation
end QEC.Coding.AlgebraicGeometry.GlobalPlace
