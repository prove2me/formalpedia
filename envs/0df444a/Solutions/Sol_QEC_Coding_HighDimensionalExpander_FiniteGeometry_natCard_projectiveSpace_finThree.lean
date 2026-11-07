-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.FiniteGeometry.natCard_projectiveSpace_finThree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:59:31.969197+00:00
-- url     : https://prove2.me/submissions/746a8eef-b092-474b-a0c7-9ec7548a31bb

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.FiniteGeometry
open Module
namespace QEC.Coding.HighDimensionalExpander.FiniteGeometry
theorem _root_.solution
    (k : Type*) [Field k] [Finite k] :
    Nat.card (Projectivization k (Fin 3 → k)) =
      Nat.card k ^ 2 + Nat.card k + 1 := by
  rw [Projectivization.card_of_finrank k (Fin 3 → k)
    (Module.finrank_fintype_fun_eq_card k)]
  norm_num [Finset.sum_range_succ]
  ring
end QEC.Coding.HighDimensionalExpander.FiniteGeometry
