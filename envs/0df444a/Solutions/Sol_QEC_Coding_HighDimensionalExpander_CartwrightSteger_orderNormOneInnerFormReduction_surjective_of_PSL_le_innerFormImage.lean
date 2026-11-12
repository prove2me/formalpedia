-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderNormOneInnerFormReduction_surjective_of_PSL_le_innerFormImage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:23:53.794135+00:00
-- url     : https://prove2.me/submissions/1ad75ed7-72fd-473e-b793-93c9e50542a7

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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_IndexInnerFormNormOnePGLImage_eq_orderNormOne_range
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_simple_le_of_normal_subgroupOf_of_exists_ne_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_PSL_isSimpleGroup


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups SphericalHecke.LocalTopology Valued
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat)
    (hPSL : PSL P r level ≤ IndexInnerFormImage P r level) :
    Function.Surjective (orderNormOneInnerFormReduction P r level) := by
  letI : IsSimpleGroup (PSL P r level) :=
    PSL_isSimpleGroup P r level
  have hne : ∃ g : PGL P r level,
      g ∈ IndexInnerFormNormOnePGLImage P r level ∧
      g ∈ PSL P r level ∧ g ≠ 1 := by
    obtain ⟨g, hg, hg1⟩ :=
      exists_ne_one_mem_range_orderNormOneInnerFormReduction P r level
    obtain ⟨x, rfl⟩ := hg
    refine ⟨(orderNormOneInnerFormReduction P r level x : PGL P r level),
      ?_, (orderNormOneInnerFormReduction P r level x).property, ?_⟩
    · rw [IndexInnerFormNormOnePGLImage_eq_orderNormOne_range]
      exact ⟨x, rfl⟩
    · intro hx
      apply hg1
      apply Subtype.ext
      exact hx
  have hcontain : PSL P r level ≤
      IndexInnerFormNormOnePGLImage P r level :=
    simple_le_of_normal_subgroupOf_of_exists_ne_one
      (PSL P r level)
      (IndexInnerFormNormOnePGLImage P r level)
      (IndexInnerFormImage P r level) hPSL hne
  intro y
  have hy : (y : PGL P r level) ∈
      IndexInnerFormNormOnePGLImage P r level :=
    hcontain y.property
  rw [IndexInnerFormNormOnePGLImage_eq_orderNormOne_range] at hy
  obtain ⟨x, hx⟩ := hy
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact hx
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
