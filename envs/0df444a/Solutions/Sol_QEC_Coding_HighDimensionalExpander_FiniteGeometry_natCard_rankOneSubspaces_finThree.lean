-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.FiniteGeometry.natCard_rankOneSubspaces_finThree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:24:51.864597+00:00
-- url     : https://prove2.me/submissions/32220b38-ab0b-4e22-9eb0-7fe05c25c706

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_FiniteGeometry_natCard_finiteGrassmannian_mul

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.FiniteGeometry
open Module
namespace QEC.Coding.HighDimensionalExpander.FiniteGeometry
theorem _root_.solution
    (k : Type*) [Field k] [Fintype k] :
    Nat.card (FiniteGrassmannian k (Fin 3 → k) 1) =
      Fintype.card k ^ 2 + Fintype.card k + 1 := by
  let q := Fintype.card k
  have h := natCard_finiteGrassmannian_mul k (Fin 3 → k) 1 (by simp)
  simp [Module.finrank_fintype_fun_eq_card] at h
  change Nat.card (FiniteGrassmannian k (Fin 3 → k) 1) * (q - 1) =
    q ^ 3 - 1 at h
  have hq : 1 < q := by
    simpa [q, Nat.card_eq_fintype_card] using (Finite.one_lt_card (α := k))
  have hfactor : (q ^ 2 + q + 1) * (q - 1) = q ^ 3 - 1 := by
    simpa [Finset.sum_range_succ, add_comm, add_left_comm, add_assoc] using
      (geom_sum_mul_of_one_le hq.le 3)
  exact Nat.eq_of_mul_eq_mul_right (Nat.sub_pos_of_lt hq) (h.trans hfactor.symm)
end QEC.Coding.HighDimensionalExpander.FiniteGeometry
