-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P16.stationaryVector_entryBound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T14:56:15.126151+00:00
-- url     : https://prove2.me/submissions/19219bf2-324a-4ff7-baf0-1beafd0b0162

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P16

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance 100] LieRing.ofAssociativeRing

open QAlgorithms.Papers.Independent.Dependency50.P16

local notation "Vec" => fun n : ℕ => Fin n → ℝ

theorem solution {n : ℕ} (hn : 2 ≤ n) (A : RMat n) (v : Vec n)
    (hdiag : ∀ i, A i i ≤ 0) (hoff : ∀ i j, i ≠ j → 0 ≤ A i j)
    (hv : ∀ i, 0 ≤ v i) (hAv : A *ᵥ v = 0) :
    ∀ i j, i ≠ j → A i j * v j ≤ maxEntryNorm A * v i := by
  intro i j hij
  have hrow : ∑ k, A i k * v k = 0 := by
    have := congrFun hAv i
    simpa [Matrix.mulVec, dotProduct] using this
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hrow
  have hle : A i j * v j ≤ ∑ k ∈ Finset.univ.erase i, A i k * v k := by
    apply Finset.single_le_sum (f := fun k => A i k * v k) _ (Finset.mem_erase.2 ⟨Ne.symm hij, Finset.mem_univ j⟩)
    intro k hk
    exact mul_nonneg (hoff i k (Ne.symm (Finset.mem_erase.1 hk).1)) (hv k)
  have hmax : -A i i ≤ maxEntryNorm A := by
    have h1 : ‖A i i‖₊ ≤ Finset.univ.sup (fun ij : Fin n × Fin n => ‖A ij.1 ij.2‖₊) :=
      Finset.le_sup (f := fun ij : Fin n × Fin n => ‖A ij.1 ij.2‖₊) (Finset.mem_univ (i, i))
    have h2 : (‖A i i‖₊ : ℝ) ≤ maxEntryNorm A := by
      unfold maxEntryNorm; exact_mod_cast h1
    have h3 : (‖A i i‖₊ : ℝ) = |A i i| := by simp
    rw [h3] at h2
    have := neg_le_abs (A i i)
    linarith
  have := mul_le_mul_of_nonneg_right hmax (hv i)
  nlinarith
