-- Prove2me | solution 1 for Planks.exists_point_outside_planks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:06:21.609942+00:00
-- url     : https://prove2.me/submissions/3abc6bf7-9065-4d83-999d-cb7c8f9dc038

module
public import Mathlib
public import Definitions.Def_BallPlank_Planks
public import Theorems.Thm_Planks_exists_minimizer
public import Theorems.Thm_Planks_stationary
public import Theorems.Thm_Planks_bang
public import Theorems.Thm_Planks_norm_sq_sum

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
theorem _root_.solution (ℓ : ι → E →L[ℝ] ℝ) (x : ι → E) (hx : Orthonormal ℝ x)
    (h : ∀ i, ℓ i (x i) = 1) :
    ∃ z : E, ‖z‖ ≤ Real.sqrt (Fintype.card ι) ∧ ∀ i, 1 ≤ |ℓ i z| := by
  obtain ⟨y, hyS, hmin, hF⟩ := exists_minimizer ℓ x hx h
  have hy0 : ∀ i, ℓ i (y i) ≠ 0 := fun i hi => by
    have := hyS.2 i
    rw [hi] at this
    norm_num at this
  have hsym : ∀ i j, ((ℓ i (y i))⁻¹) ^ 3 * ℓ i (y j) = ((ℓ j (y j))⁻¹) ^ 3 * ℓ j (y i) :=
    fun i j => if hij : i = j then by subst hij; rfl else stationary ℓ y hyS hmin hF i j hij
  obtain ⟨ε, hε⟩ := bang ℓ y hy0 hsym
  refine ⟨_, ?_, hε⟩
  rw [← Real.sqrt_sq (norm_nonneg _)]
  apply Real.sqrt_le_sqrt
  rw [norm_sq_sum y hyS.1]
  calc ∑ i, (sgn (ε i) * (ℓ i (y i))⁻¹) ^ 2 = objF ℓ y := by
        unfold objF
        refine Finset.sum_congr rfl fun i _ => ?_
        have : sgn (ε i) ^ 2 = 1 := by unfold sgn; split_ifs <;> norm_num
        rw [mul_pow, this, one_mul]
    _ ≤ _ := hF
end Planks
