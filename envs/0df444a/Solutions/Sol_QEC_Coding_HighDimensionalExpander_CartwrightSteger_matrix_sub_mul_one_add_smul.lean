-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.matrix_sub_mul_one_add_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:20:19.022873+00:00
-- url     : https://prove2.me/submissions/d6ffb448-fa75-4ef6-b17c-5a0e5b865177

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]
    (X N S : Matrix n n K) (s : K) :
    (X - N) * (1 + s • S) =
      X - N + s • (X * S - N * S) := by
  rw [mul_add, mul_one, mul_smul_comm, sub_mul, smul_sub]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
