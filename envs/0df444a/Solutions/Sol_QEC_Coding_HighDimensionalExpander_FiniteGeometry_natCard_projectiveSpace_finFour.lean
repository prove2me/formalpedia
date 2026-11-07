-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.FiniteGeometry.natCard_projectiveSpace_finFour
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:59:33.255441+00:00
-- url     : https://prove2.me/submissions/c0fbdd32-1c97-447f-bf00-7f035878867e

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
    Nat.card (Projectivization k (Fin 4 → k)) =
      Nat.card k ^ 3 + Nat.card k ^ 2 + Nat.card k + 1 := by
  rw [Projectivization.card_of_finrank k (Fin 4 → k)
    (Module.finrank_fintype_fun_eq_card k)]
  norm_num [Finset.sum_range_succ]
  ring
end QEC.Coding.HighDimensionalExpander.FiniteGeometry
