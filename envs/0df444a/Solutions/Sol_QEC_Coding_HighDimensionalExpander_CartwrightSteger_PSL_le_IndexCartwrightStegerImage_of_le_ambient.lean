-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.PSL_le_IndexCartwrightStegerImage_of_le_ambient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:19:14.990642+00:00
-- url     : https://prove2.me/submissions/168cfa42-29ce-40dd-9c8b-3d9fbd457026

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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_simple_le_of_normal_subgroupOf_of_exists_ne_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_PSL_isSimpleGroup
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_nontrivial_mem_image_inter_PSL


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups SphericalHecke.LocalTopology Valued
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat)
    (hPSL : PSL P r level ≤ IndexCartwrightStegerAmbient P r level) :
    PSL P r level ≤ IndexCartwrightStegerImage P r level := by
  letI : IsSimpleGroup (PSL P r level) :=
    PSL_isSimpleGroup P r level
  exact simple_le_of_normal_subgroupOf_of_exists_ne_one
    (PSL P r level)
    (IndexCartwrightStegerImage P r level)
    (IndexCartwrightStegerAmbient P r level)
    hPSL (exists_nontrivial_mem_image_inter_PSL P r level)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
