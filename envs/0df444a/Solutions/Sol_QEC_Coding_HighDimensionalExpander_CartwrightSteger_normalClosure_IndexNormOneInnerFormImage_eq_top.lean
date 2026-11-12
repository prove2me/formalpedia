-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.normalClosure_IndexNormOneInnerFormImage_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:47:34.411317+00:00
-- url     : https://prove2.me/submissions/2ef0ef57-42c9-4503-a121-8fb08379d71f

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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_IndexNormOneInnerFormImage_ne_bot
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_PSL_isSimpleGroup


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups SphericalHecke.LocalTopology Valued
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup.normalClosure
        (IndexNormOneInnerFormImage P r level : Set (PSL P r level)) = ⊤ := by
  letI : IsSimpleGroup (PSL P r level) :=
    PSL_isSimpleGroup P r level
  apply Subgroup.normalClosure_normal.eq_bot_or_eq_top.resolve_left
  intro hbot
  apply IndexNormOneInnerFormImage_ne_bot P r level
  apply le_antisymm
  · intro g hg
    have hclosure : g ∈ Subgroup.normalClosure
        (IndexNormOneInnerFormImage P r level : Set (PSL P r level)) :=
      Subgroup.subset_normalClosure hg
    rw [hbot, Subgroup.mem_bot] at hclosure
    exact hclosure
  · exact bot_le
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
