-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.globalSimplePoleResidueSum_finset_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:48:17.629204+00:00
-- url     : https://prove2.me/submissions/9e79b6b3-b231-46d6-8bce-93dd072685ce

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_SimplePoleResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_SimplePoleResidueLinear
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_globalSimplePoleResidueSum_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_globalSimplePoleResidueSum_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.Differential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
namespace QEC.Coding.AlgebraicGeometry.Differential
theorem _root_.solution {ι : Type*} (s : Finset ι)
    (omega : ι → Differential k F)
    (homega : ∀ i, IsGlobalSimplePole (k := k) (F := F) (omega i)) :
    globalSimplePoleResidueSum (k := k) (F := F) (∑ i ∈ s, omega i)
        (IsGlobalSimplePole.finset_sum s omega homega) =
      ∑ i ∈ s, globalSimplePoleResidueSum (k := k) (F := F)
        (omega i) (homega i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.notMem_empty, Finset.sum_empty] using
        (globalSimplePoleResidueSum_zero (k := k) (F := F))
  | @insert i s hi ih =>
      calc
        globalSimplePoleResidueSum (k := k) (F := F)
            (∑ j ∈ insert i s, omega j)
            (IsGlobalSimplePole.finset_sum (insert i s) omega homega) =
            globalSimplePoleResidueSum (k := k) (F := F)
                (omega i) (homega i) +
              globalSimplePoleResidueSum (k := k) (F := F)
                (∑ j ∈ s, omega j)
                (IsGlobalSimplePole.finset_sum s omega homega) := by
          simpa only [Finset.sum_insert hi] using
            (globalSimplePoleResidueSum_add (k := k) (F := F)
              (omega i) (∑ j ∈ s, omega j) (homega i)
              (IsGlobalSimplePole.finset_sum s omega homega))
        _ = ∑ j ∈ insert i s, globalSimplePoleResidueSum
              (k := k) (F := F) (omega j) (homega j) := by
          rw [ih, Finset.sum_insert hi]
end QEC.Coding.AlgebraicGeometry.Differential
