-- Prove2me | solution 1 for Planks.planks_not_cover_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:12:08.87735+00:00
-- url     : https://prove2.me/submissions/c8bcf52c-99d9-40a9-878f-a7561d483ee0

module
public import Mathlib
public import Definitions.Def_BallPlank_Planks
public import Theorems.Thm_Planks_exists_point_outside_planks

set_option autoImplicit true
@[expose] public section
public section
open scoped RealInnerProductSpace
open Classical
noncomputable section
open Planks
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι]
namespace Planks
theorem _root_.solution (n : ℕ)
    (x : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (ℓ : Fin n → Module.Dual ℝ (EuclideanSpace ℝ (Fin n)))
    (h : ∀ i, ℓ i (x i) = 1) :
    ¬ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt n) ⊆ ⋃ i, plank (ℓ i)) := by
  intro hcov
  obtain ⟨z, hz, hz'⟩ := exists_point_outside_planks
    (fun i => LinearMap.toContinuousLinearMap (ℓ i)) x x.orthonormal (by simpa using h)
  have hmem := hcov (mem_closedBall_zero_iff.mpr (by simpa using hz))
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
  have := hz' i
  simp only [plank, Set.mem_ofPred_eq] at hi
  simp at this
  linarith
end Planks
