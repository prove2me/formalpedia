-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.maximalIdeal_eq_span_uniformizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:16:21.456261+00:00
-- url     : https://prove2.me/submissions/5be4730f-4898-40e6-83d1-8bb58c12e200

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_Differential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlace
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_residueCongruent_refl
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_residueCongruent_symm
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_residueCongruent_trans
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuation_uniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


attribute [local refl] QEC.Coding.AlgebraicGeometry.Differential.residueCongruent_refl
attribute [local symm] QEC.Coding.AlgebraicGeometry.Differential.residueCongruent_symm
attribute [local trans] QEC.Coding.AlgebraicGeometry.Differential.residueCongruent_trans
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
private theorem uniformizerInValuationRing_isUniformizer (P : GlobalPlace k F)
    [P.valuation.IsRankOneDiscrete] :
    P.valuation.IsUniformizer (P.uniformizerInValuationRing : F) := by
  letI : P.valuation.IsNontrivial := valuation_isNontrivial P
  letI : IsCyclic (MonoidWithZeroHom.valueGroup (.ofClass P.valuation)) := inferInstance
  letI : Nontrivial (MonoidWithZeroHom.valueGroup (.ofClass P.valuation)) := inferInstance
  change P.valuation P.uniformizer =
    (Valuation.IsRankOneDiscrete.generator P.valuation : ℤᵐ⁰)
  calc
    P.valuation P.uniformizer = WithZero.exp (-1 : ℤ) :=
      P.valuation_uniformizer
    _ = (Valuation.IsRankOneDiscrete.generator P.valuation : ℤᵐ⁰) := by
      simpa using congrArg (fun u : ℤᵐ⁰ˣ => (u : ℤᵐ⁰))
        (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
          (v := P.valuation) P.normalized).symm
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
    IsLocalRing.maximalIdeal P.valuationRing =
      Ideal.span ({P.uniformizerInValuationRing} : Set P.valuationRing) := by
  letI : P.valuation.IsNontrivial := valuation_isNontrivial P
  letI : IsCyclic (MonoidWithZeroHom.valueGroup (.ofClass P.valuation)) := inferInstance
  letI : Nontrivial (MonoidWithZeroHom.valueGroup (.ofClass P.valuation)) := inferInstance
  letI : P.valuation.IsRankOneDiscrete :=
    Valuation.IsRankOneDiscrete.mk' P.valuation
  exact (uniformizerInValuationRing_isUniformizer P).is_generator
end QEC.Coding.AlgebraicGeometry.GlobalPlace
