-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_eq_algebraMap_of_constantFrobenius_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:29:17.632545+00:00
-- url     : https://prove2.me/submissions/d9f2acb5-9636-419b-84a4-603c8d8bf494

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_zpowers_constantFrobenius_eq_top

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r)
    (hc : constantFrobenius P r c = c) :
    ∃ a : BaseField P,
      algebraMap (BaseField P) (ConstantExtension P r) a = c := by
  rw [← Set.mem_range]
  apply (IsGalois.mem_range_algebraMap_iff_fixed
    (F := BaseField P) (E := ConstantExtension P r) c).mpr
  intro f
  have hle :
      Subgroup.zpowers (constantFrobenius P r) ≤
        MulAction.stabilizer
          (ConstantExtension P r ≃ₐ[BaseField P] ConstantExtension P r) c := by
    rw [Subgroup.zpowers_le]
    exact MulAction.mem_stabilizer_iff.mpr hc
  exact MulAction.mem_stabilizer_iff.mp
    (hle (by rw [zpowers_constantFrobenius_eq_top P r]; exact Subgroup.mem_top f))
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
