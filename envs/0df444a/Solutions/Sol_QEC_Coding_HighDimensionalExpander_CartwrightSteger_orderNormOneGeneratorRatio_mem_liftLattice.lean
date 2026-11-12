-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderNormOneGeneratorRatio_mem_liftLattice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:17:36.200498+00:00
-- url     : https://prove2.me/submissions/ba48962d-e12c-4a2b-9bc6-ecdaab2fcc3b

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_SimpleTransitivity
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_SpecialLinear
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicDivisionAlgebra
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.Algebra.Central.Matrix
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_StrongApproximation

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups SphericalHecke.LocalTopology Valued
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank)
    (u v : ConstantProjectiveClass P r) :
    orderNormOneGeneratorRatio P r u v ∈
      OrderNormOneCartwrightStegerLiftLattice P r := by
  change Matrix.SpecialLinearGroup.toGL
      (orderSplitGeneratorRatioSpecial P r u v) ∈
    OrderSplitCartwrightStegerLattice P r
  have hu : orderSplitCartwrightStegerGeneratorGL P r
        (constantClassRepresentative P r u) ∈
      OrderSplitCartwrightStegerLattice P r :=
    Subgroup.subset_closure ⟨u, rfl⟩
  have hv : orderSplitCartwrightStegerGeneratorGL P r
        (constantClassRepresentative P r v) ∈
      OrderSplitCartwrightStegerLattice P r :=
    Subgroup.subset_closure ⟨v, rfl⟩
  have hto : Matrix.SpecialLinearGroup.toGL
        (orderSplitGeneratorRatioSpecial P r u v) =
      orderSplitCartwrightStegerGeneratorGL P r
          (constantClassRepresentative P r u) *
        (orderSplitCartwrightStegerGeneratorGL P r
          (constantClassRepresentative P r v))⁻¹ := by
    apply Units.ext
    rfl
  rw [hto]
  have hratio := (OrderSplitCartwrightStegerLattice P r).mul_mem
    hu ((OrderSplitCartwrightStegerLattice P r).inv_mem hv)
  exact hratio
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
