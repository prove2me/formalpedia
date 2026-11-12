-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.IndexNormOneInnerFormImage_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:13:44.849166+00:00
-- url     : https://prove2.me/submissions/119173ca-7754-4a24-aba5-1578bc5f1dff

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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_ne_one_mem_range_orderNormOneInnerFormReduction

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups SphericalHecke.LocalTopology Valued
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexNormOneInnerFormImage P r level ≠ ⊥ := by
  obtain ⟨g, hg, hgne⟩ :=
    exists_ne_one_mem_range_orderNormOneInnerFormReduction P r level
  intro hbot
  have : g = 1 := by
    rw [← Subgroup.mem_bot, ← hbot]
    exact hg
  exact hgne this
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
