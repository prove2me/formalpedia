-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.FiniteGeometry.mem_coordinateGrassmannian_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:20:51.992319+00:00
-- url     : https://prove2.me/submissions/5852ced8-7c1e-45c8-ab04-322b2d739a62

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.FiniteGeometry
open Module
namespace QEC.Coding.HighDimensionalExpander.FiniteGeometry
theorem _root_.solution
    (k : Type*) [Field k] (d r : ℕ) (hr : r ≤ d)
    (v : Fin d → k) :
    v ∈ (coordinateGrassmannian k d r hr).1 ↔
      ∀ i : Fin d, r ≤ i.val → v i = 0 := by
  constructor
  · intro hv
    change v ∈ Submodule.span k (Set.range (coordinateFrame k d r hr)) at hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨j, rfl⟩ := hx
        intro i hi
        have hne : i ≠ Fin.castLE hr j := by
          intro h
          have : r ≤ j.val := by simpa [h] using hi
          exact (Nat.not_le_of_lt j.isLt) this
        simp [coordinateFrame, hne]
    | zero => simp
    | add x y _ _ hx hy =>
        intro i hi
        simp [hx i hi, hy i hi]
    | smul a x _ hx =>
        intro i hi
        simp [hx i hi]
  · intro hv
    change v ∈ Submodule.span k (Set.range (coordinateFrame k d r hr))
    have hsum : v = ∑ j : Fin r, v (Fin.castLE hr j) • coordinateFrame k d r hr j := by
      funext i
      simp only [Finset.sum_apply, Pi.smul_apply]
      by_cases hi : i.val < r
      · let j : Fin r := ⟨i.val, hi⟩
        rw [show i = Fin.castLE hr j by apply Fin.ext; rfl]
        rw [Finset.sum_eq_single j]
        · simp [coordinateFrame]
        · intro b _ hb
          have hne : Fin.castLE hr j ≠ Fin.castLE hr b := by
            intro h
            apply hb
            exact Fin.castLE_injective hr h.symm
          simp [coordinateFrame, hne]
        · simp
      · have hzero : v i = 0 := hv i (Nat.le_of_not_gt hi)
        rw [hzero]
        symm
        apply Finset.sum_eq_zero
        intro j _
        have hne : i ≠ Fin.castLE hr j := by
          intro h
          have : i.val < r := by simpa [h] using j.isLt
          exact hi this
        simp [coordinateFrame, hne]
    rw [hsum]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
end QEC.Coding.HighDimensionalExpander.FiniteGeometry
