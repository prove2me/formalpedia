-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.IndexInnerFormNormOnePGLImage_eq_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:16:26.897329+00:00
-- url     : https://prove2.me/submissions/5b789a6c-db63-44f6-b399-7f1850dd803b

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
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexInnerFormNormOnePGLImage P r level =
      (orderInnerFormNormOneReductionToPGL P r level).range := by
  ext g
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨x, hx, hxa⟩ := ha
    refine ⟨⟨x, hx⟩, ?_⟩
    exact congrArg Subtype.val hxa
  · rintro ⟨x, rfl⟩
    refine ⟨orderInnerFormReductionToImage P r level
        (x : OrderInnerFormUnits P r), ?_, rfl⟩
    exact ⟨x, x.property, rfl⟩
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
