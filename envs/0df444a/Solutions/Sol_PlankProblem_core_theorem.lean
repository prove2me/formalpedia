-- Prove2me | solution 1 for PlankProblem.core_theorem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:11:33.639602+00:00
-- url     : https://prove2.me/submissions/5eec87e7-203b-4233-af39-5df9075ac016

module
public import Definitions.Def_BallPlank_ShiftedPlanks
public import Definitions.Def_BallPlank_BallPlankFinal
public import Theorems.Thm_Planks_exists_point_outside_shifted_planks


set_option autoImplicit true
@[expose] public section
public section
open Set
open scoped BigOperators InnerProductSpace Pointwise
noncomputable section
open PlankProblem
variable {n : ℕ}
local notation "Rn" => EuclideanSpace ℝ (Fin n)
namespace PlankProblem
theorem _root_.solution
    (X : OrthonormalBasis (Fin n) ℝ Rn)
    (ℓ : Fin n → (Rn →ₗ[ℝ] ℝ))
    (hℓ : ∀ i, ℓ i (X i) = 1)
    (c : Fin n → ℝ) :
    ∃ z : Rn,
      ‖z‖ ≤ Real.sqrt (n : ℝ) ∧
      ∀ i, 1 ≤ |ℓ i z - c i| := by
  obtain ⟨z, hz, hz'⟩ := Planks.exists_point_outside_shifted_planks
    (fun i => LinearMap.toContinuousLinearMap (ℓ i)) c X X.orthonormal (by simpa using hℓ)
  exact ⟨z, by simpa using hz, fun i => by simpa using hz' i⟩
end PlankProblem
