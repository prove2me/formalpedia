-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P25.strongContinuity_iff_quadraticContinuity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T14:35:09.377987+00:00
-- url     : https://prove2.me/submissions/c29b7323-033a-4188-93a4-bec050d548ce

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P25
noncomputable section

open Set Filter Topology

open scoped Classical ENNReal

open QAlgorithms.Papers.Independent.Next46.P25

universe u v w z

attribute [local instance 100] LieRing.ofAssociativeRing

theorem solution
    {g : Type u} [LieRing g] [LieAlgebra ℝ g] [UniformSpace g]
    [IsUniformAddGroup g] [T2Space g] [ContinuousSMul ℝ g]
    [LocallyConvexSpace ℝ g] [TopologicalSpace.MetrizableSpace g] [CompleteSpace g]
    {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]
    (hBracket : Continuous (fun xy : g × g => ⁅xy.1, xy.2⁆))
    (rho : g →ₗ⁅ℝ⁆ Module.End ℂ V)
    (hSkew : ∀ (x : g) (v w : V),
      inner ℂ w (rho x v) = -inner ℂ (rho x w) v) :
    StronglyContinuous (fun x v => rho x v) ↔
      ∀ v : V, Continuous (fun x : g => (inner ℂ v (rho x (rho x v))).re) := by
  have key : ∀ (x : g) (v : V), (inner ℂ v (rho x (rho x v))).re = -‖rho x v‖ ^ 2 := by
    intro x v
    rw [hSkew x (rho x v) v, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  constructor
  · intro h v
    simp_rw [key]
    exact ((h v).norm.pow 2).neg
  · intro h v
    let f : g →+ V :=
      { toFun := fun x => rho x v
        map_zero' := by simp
        map_add' := fun x y => by simp }
    have hc : Continuous f := by
      apply continuous_of_continuousAt_zero f
      have h0 : f 0 = 0 := by simp [f]
      rw [ContinuousAt, h0, tendsto_zero_iff_norm_tendsto_zero]
      have hq : Continuous (fun x : g => Real.sqrt (-(inner ℂ v (rho x (rho x v))).re)) :=
        ((h v).neg).sqrt
      have heq : (fun x : g => Real.sqrt (-(inner ℂ v (rho x (rho x v))).re)) =
          fun x => ‖f x‖ := by
        funext x; rw [key]; simp [f, Real.sqrt_sq (norm_nonneg _)]
      rw [heq] at hq
      have := hq.tendsto 0
      simpa [h0] using this
    exact hc
