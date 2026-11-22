-- Prove2me | solution 1 for Positive.continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:18:11.210799+00:00
-- url     : https://prove2.me/submissions/8e6f768e-098b-4c0c-8288-4c2950525dbf

module
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Mathlib.Algebra.Order.Module.Basic
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.Equiv
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Operators_Positive
public import Theorems.Thm_Positive_monotone_iff
public import Theorems.Thm_Positive_abs_le_map_abs
public import Theorems.Thm_Positive_extension_apply
attribute [local simp] Positive.extension_apply
section
@[expose] public section
variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] [Lattice X] [Lattice Y]
  [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y] [VectorLattice X] [VectorLattice Y]
namespace Positive
section ExtensionLemma
variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] [Lattice X] [Lattice Y]
  [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y] [VectorLattice X] [VectorLattice Y]
  [IsVLArchimedean Y] {τ : X → Y}
variable
  (hτ_nn : ∀ x, 0 ≤ x → 0 ≤ τ x)
  (hτ_add : ∀ x y, 0 ≤ x → 0 ≤ y → τ (x + y) = τ x + τ y)
end ExtensionLemma
variable {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [Lattice X] [Lattice Y] [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
  [BanachLattice X] [NormedVectorLattice Y]
private lemma norm_map_le_of_abs_le {f : X →ₗ[ℝ] Y} (hf : Positive f)
    {x y : X} (h : |x| ≤ y) : ‖f x‖ ≤ ‖f y‖ :=
  norm_le_norm_of_abs_le_abs <|
    (abs_le_map_abs hf x).trans <|
    ((monotone_iff.mpr hf) h).trans (le_abs_self _)
end Positive
end
end

set_option autoImplicit true
@[expose] public section
public section
variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] [Lattice X] [Lattice Y]
  [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y] [VectorLattice X] [VectorLattice Y]
open Positive
variable {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [Lattice X] [Lattice Y] [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
  [BanachLattice X] [NormedVectorLattice Y]
namespace Positive
theorem _root_.solution {f : X →ₗ[ℝ] Y} (hf : Positive f) : Continuous f := by
  by_contra hcont
  have hunb : ∀ C : ℝ, ∃ x : X, C * ‖x‖ < ‖f x‖ := by
    by_contra h; push Not at h; obtain ⟨C, hC⟩ := h
    exact hcont (continuous_of_linear_of_bound f.map_add f.map_smul hC)
  -- For each n, find xₙ with ‖xₙ‖ ≤ (1/2)ⁿ and n < ‖f xₙ‖
  have hseq : ∀ n : ℕ, ∃ x : X, ‖x‖ ≤ (1 / 2 : ℝ) ^ n ∧ (n : ℝ) < ‖f x‖ := by
    intro n
    obtain ⟨z, hz⟩ := hunb ((n : ℝ) * (2 : ℝ) ^ n)
    have hznz : z ≠ 0 := by intro h; simp [h] at hz
    refine ⟨((2 : ℝ) ^ n * ‖z‖)⁻¹ • z, ?_, ?_⟩
    · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (by positivity))]
      rw [inv_mul_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ n * ‖z‖)]
      simp [one_div, mul_comm]
    · rw [map_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (by positivity))]
      rw [lt_inv_mul_iff₀ (by positivity : (0 : ℝ) < 2 ^ n * ‖z‖)]
      linarith [mul_comm ((n : ℝ) * (2 : ℝ) ^ n) ‖z‖]
  choose x hxn hxf using hseq
  have habs : Summable (fun n => |x n|) :=
    .of_norm_bounded (g := fun n => (1 / 2 : ℝ) ^ n)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))
      (fun n => by rw [norm_abs_eq_norm]; exact hxn n)
  set y := ∑' n, |x n|
  have hle : ∀ n, |x n| ≤ y := fun n => habs.le_tsum n (fun j _ => abs_nonneg _)
  obtain ⟨N, hN⟩ := exists_nat_gt ‖f y‖
  exact absurd (lt_of_lt_of_le (hxf N) (norm_map_le_of_abs_le hf (hle N)))
    (not_lt.mpr hN.le)
end Positive
