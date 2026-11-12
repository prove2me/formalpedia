-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.IndexNormOneCartwrightStegerLiftPGLImage_le_indexImage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:49:42.585269+00:00
-- url     : https://prove2.me/submissions/034f444a-f6e5-4442-9103-9059d2e15264

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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderNormOneInnerFormReductionToPGL_eq_orderSplitReduction

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups SphericalHecke.LocalTopology Valued
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexNormOneCartwrightStegerLiftPGLImage P r level ≤
      IndexCartwrightStegerImage P r level := by
  rintro y ⟨g, hg, rfl⟩
  obtain ⟨x, hx, rfl⟩ := hg
  rw [← map_OrderSplitCartwrightStegerLattice P r level]
  refine ⟨orderNormOneInnerFormToSplitGL P r x, hx, ?_⟩
  exact (orderNormOneInnerFormReductionToPGL_eq_orderSplitReduction
    P r level x).symm
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
