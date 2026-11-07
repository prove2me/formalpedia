-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.FiniteGeometry.natCard_rankThreeSubspaces_finFour
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:24:54.789498+00:00
-- url     : https://prove2.me/submissions/2acb7e30-39ce-44f3-b4d4-143d5a835df1

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
    Nat.card (FiniteGrassmannian k (Fin 4 → k) 3) =
      Fintype.card k ^ 3 + Fintype.card k ^ 2 + Fintype.card k + 1 := by
  let q := Fintype.card k
  have h := natCard_finiteGrassmannian_mul k (Fin 4 → k) 3 (by simp)
  simp [Module.finrank_fintype_fun_eq_card, Fin.prod_univ_succ] at h
  change Nat.card (FiniteGrassmannian k (Fin 4 → k) 3) *
      ((q ^ 3 - 1) * ((q ^ 3 - q) * (q ^ 3 - q ^ 2))) =
    (q ^ 4 - 1) * ((q ^ 4 - q) * (q ^ 4 - q ^ 2)) at h
  have hq : 1 < q := by
    simpa [q, Nat.card_eq_fintype_card] using (Finite.one_lt_card (α := k))
  have hq1 := hq.le
  have h21 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    simpa [Finset.sum_range_succ, add_comm, add_left_comm, add_assoc,
      mul_comm] using (geom_sum_mul_of_one_le hq1 2).symm
  have h31 : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by
    simpa [Finset.sum_range_succ, add_comm, add_left_comm, add_assoc,
      mul_comm] using (geom_sum_mul_of_one_le hq1 3).symm
  have h3q : q ^ 3 - q = q * (q - 1) * (q + 1) := by
    calc
      q ^ 3 - q = q * q ^ 2 - q * 1 := by congr 1 <;> ring
      _ = q * (q ^ 2 - 1) := (Nat.mul_sub_left_distrib q (q ^ 2) 1).symm
      _ = _ := by rw [h21]; ring
  have h3q2 : q ^ 3 - q ^ 2 = q ^ 2 * (q - 1) := by
    calc
      q ^ 3 - q ^ 2 = q ^ 2 * q - q ^ 2 * 1 := by congr 1 <;> ring
      _ = _ := (Nat.mul_sub_left_distrib (q ^ 2) q 1).symm
  have h41 : q ^ 4 - 1 = (q - 1) * (q ^ 3 + q ^ 2 + q + 1) := by
    simpa [Finset.sum_range_succ, add_comm, add_left_comm, add_assoc,
      mul_comm] using (geom_sum_mul_of_one_le hq1 4).symm
  have h4q : q ^ 4 - q = q * (q - 1) * (q ^ 2 + q + 1) := by
    calc
      q ^ 4 - q = q * q ^ 3 - q * 1 := by congr 1 <;> ring
      _ = q * (q ^ 3 - 1) := (Nat.mul_sub_left_distrib q (q ^ 3) 1).symm
      _ = _ := by rw [h31]; ring
  have h4q2 : q ^ 4 - q ^ 2 = q ^ 2 * (q - 1) * (q + 1) := by
    calc
      q ^ 4 - q ^ 2 = q ^ 2 * q ^ 2 - q ^ 2 * 1 := by congr 1 <;> ring
      _ = q ^ 2 * (q ^ 2 - 1) :=
        (Nat.mul_sub_left_distrib (q ^ 2) (q ^ 2) 1).symm
      _ = _ := by rw [h21]; ring
  have hfactor : (q ^ 3 + q ^ 2 + q + 1) *
      ((q ^ 3 - 1) * ((q ^ 3 - q) * (q ^ 3 - q ^ 2))) =
    (q ^ 4 - 1) * ((q ^ 4 - q) * (q ^ 4 - q ^ 2)) := by
    rw [h31, h3q, h3q2, h41, h4q, h4q2]
    ring
  have hden : 0 < (q ^ 3 - 1) * ((q ^ 3 - q) * (q ^ 3 - q ^ 2)) := by
    rw [h31, h3q, h3q2]
    have hqm : 0 < q - 1 := Nat.sub_pos_of_lt hq
    positivity
  exact Nat.eq_of_mul_eq_mul_right hden (h.trans hfactor.symm)
end QEC.Coding.HighDimensionalExpander.FiniteGeometry
