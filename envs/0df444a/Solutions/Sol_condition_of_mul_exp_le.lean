-- Prove2me | solution 1 for condition_of_mul_exp_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:39:37.905084+00:00
-- url     : https://prove2.me/submissions/621812ba-683f-483c-a307-005a247b361b

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
theorem _root_.solution {k m : ℕ} (hk : k ≠ 0) (hm : m ≠ 0)
    (hm : m ^ 2 * k * Real.exp (-m / k + 1) ≤ 1) :
    polychromColouringBound k m := by
  have : 0 ≤ 1 - (k : ℝ)⁻¹ := by
    simp only [sub_nonneg]
    apply inv_le_one_of_one_le₀ (by simp; lia)
  calc
    _ ≤ Real.exp 1 * m ^ 2 * k * (1 - (k : ℝ)⁻¹) ^ m := by
      gcongr
      have : (1 : ℝ) ≤ m := by simp; lia
      linear_combination this
    _ = Real.exp 1 * m ^ 2 * k * ((-k : ℝ)⁻¹ + 1) ^ m := by ring
    _ ≤ Real.exp 1 * m ^ 2 * k * Real.exp ((- k : ℝ)⁻¹) ^ m := by
      gcongr
      · simpa
      exact Real.add_one_le_exp _
    _ = m ^ 2 * k * (Real.exp 1 * Real.exp (- m / k)) := by
      rw [← Real.exp_nat_mul]
      ring_nf
    _ = m ^ 2 * k * Real.exp (- m / k + 1) := by grind [Real.exp_add]
    _ ≤ 1 := hm
