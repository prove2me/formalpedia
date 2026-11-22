-- Prove2me | solution 1 for condition_of_mul_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:45:35.976702+00:00
-- url     : https://prove2.me/submissions/a158633f-2937-41c8-bdee-282de832e40d

import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.NNRat.Floor
import Mathlib.Tactic.Rify
import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_Compactness
import Definitions.Def_Polychromatic_LocalLemma
import Definitions.Def_Polychromatic_Existence
import Theorems.Thm_condition_of_mul_exp_le
import Theorems.Thm_polychromColouringBound_mono
import Theorems.Thm_polychromColouringBound_zero
import Theorems.Thm_polychromColouringBound_one
import Theorems.Thm_polychromColouringBound_two_of_ge
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ



set_option autoImplicit true
open Finset
open Pointwise
variable {G : Type*} [AddCommGroup G]
open MeasureTheory ProbabilityTheory
open Real
theorem _root_.solution {k m : ℕ} (hm : 3 * k ^ 2 ≤ m) :
    polychromColouringBound k m := by
  obtain rfl | rfl | rfl | hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k := by omega
  · exact polychromColouringBound_zero
  · exact polychromColouringBound_one (by lia)
  · exact polychromColouringBound_two_of_ge (by lia)
  apply polychromColouringBound_mono (by lia) _ hm
  swap
  · linear_combination (3 * k + 7) * hk
  apply condition_of_mul_exp_le (by lia) (ne_of_gt <| by linear_combination ((3 * k + 9) * hk))
  have hk₀ : k ≠ 0 := by grind
  let g (k : ℕ) : ℝ := k ^ 5 * Real.exp (-(3 * k) + 1)
  suffices 9 * g k ≤ 1 by
    simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, ge_iff_le]
    field_simp
    linear_combination this
  have : 9 * g 3 ≤ 1 := by
    suffices 2187 * Real.exp (-1) ^ 8 ≤ 1 by
      rw [← Real.exp_nat_mul] at this
      norm_num [g, ← mul_assoc]
      norm_num at this
      exact this
    grw [Real.exp_neg_one_lt_d9]
    norm_num
  suffices AntitoneOn g {x | 3 ≤ x} by
    grw [this (by simp) hk hk]
    assumption
  apply antitoneOn_nat_Ici_of_succ_le
  intro n hn
  simp only [g]
  suffices (1 / n + 1) ^ 5 ≤ Real.exp 3 by
    simp only [Nat.cast_add_one, mul_add_one, neg_add_rev, Real.exp_add, ← mul_assoc, Real.exp_neg]
    gcongr ?_ * _ * _
    grw [← this]
    rw [← inv_pow, ← mul_pow]
    gcongr
    simp [field, add_comm]
  grw [Real.add_one_le_exp, ← Real.exp_nat_mul, hn]
  gcongr
  norm_num
