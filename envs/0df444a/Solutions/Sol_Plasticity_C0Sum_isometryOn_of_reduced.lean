-- Prove2me | solution 1 for Plasticity.C0Sum.isometryOn_of_reduced
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-19T19:04:07.589807+00:00
-- url     : https://prove2.me/submissions/9b39ee30-fcb4-4fb0-b04a-98b73e58b2c4

import Definitions.Def_Plasticity_C0Sum
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Strict.Extreme
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.EMetricSpace.Lipschitz
import Theorems.Thm_Plasticity_C0Sum_exists_blockEquiv
import Theorems.Thm_Plasticity_C0Sum_exists_extremeRule
import Theorems.Thm_Plasticity_Plane_exists_linearIsometryEquiv_of_radial_le
import Theorems.Thm_Plasticity_C0Sum_isometryOn_of_extreme_eq

open Plasticity

namespace Sol_Plasticity_C0Sum_isometryOn_of_reduced

open Metric Set

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Extreme points of the unit ball of a line are unit vectors. -/
theorem norm_eq_one_of_line (hV : Module.finrank ℝ V = 1) {x : V}
    (hx : x ∈ extremePoints ℝ (closedBall (0 : V) 1)) : ‖x‖ = 1 := by
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hV
  simpa using extremePoints_closedBall_subset_sphere hx

/-- The unit ball of a line has an extreme point (Krein–Milman). -/
theorem extremePoints_nonempty_of_line (hV : Module.finrank ℝ V = 1) :
    (extremePoints ℝ (closedBall (0 : V) 1)).Nonempty := by
  have : FiniteDimensional ℝ V := Module.finite_of_finrank_eq_succ hV
  exact (isCompact_closedBall (0 : V) 1).extremePoints_nonempty
    ⟨0, mem_closedBall_self zero_le_one⟩

/-- Scalar blocks: an odd map of extreme points between two lines is inverted by a linear
isometry. -/
theorem exists_linearIsometryEquiv_of_line (hV : Module.finrank ℝ V = 1)
    (hW : Module.finrank ℝ W = 1) (g : W → V)
    (hext : MapsTo g (extremePoints ℝ (closedBall (0 : W) 1))
      (extremePoints ℝ (closedBall (0 : V) 1)))
    (hodd : ∀ w ∈ extremePoints ℝ (closedBall (0 : W) 1), g (-w) = -g w) :
    ∃ L : V ≃ₗᵢ[ℝ] W, ∀ w ∈ extremePoints ℝ (closedBall (0 : W) 1), L (g w) = w := by
  have : FiniteDimensional ℝ V := Module.finite_of_finrank_eq_succ hV
  have : FiniteDimensional ℝ W := Module.finite_of_finrank_eq_succ hW
  obtain ⟨w0, hw0⟩ := extremePoints_nonempty_of_line hW
  have hw0n : ‖w0‖ = 1 := norm_eq_one_of_line hW hw0
  have hv0n : ‖g w0‖ = 1 := norm_eq_one_of_line hV (hext hw0)
  have hv0ne : g w0 ≠ 0 := by
    intro h; rw [h, norm_zero] at hv0n; exact zero_ne_one hv0n
  have hw0ne : w0 ≠ 0 := by
    intro h; rw [h, norm_zero] at hw0n; exact zero_ne_one hw0n
  have hVspan := (finrank_eq_one_iff_of_nonzero' (g w0) hv0ne).1 hV
  have hWspan := (finrank_eq_one_iff_of_nonzero' w0 hw0ne).1 hW
  obtain ⟨φ, -, hφv⟩ := exists_dual_vector ℝ (g w0) (by rw [hv0n]; exact one_ne_zero)
  replace hφv : φ (g w0) = 1 := by simpa [hv0n] using hφv
  let f : V →ₗᵢ[ℝ] W :=
    { toLinearMap := (φ.smulRight w0 : V →L[ℝ] W).toLinearMap
      norm_map' := by
        intro v
        obtain ⟨c, rfl⟩ := hVspan v
        simp [hφv, hv0n, hw0n, norm_smul] }
  have hf : ∀ v, f v = φ v • w0 := fun v => rfl
  refine ⟨f.toLinearIsometryEquiv (hV.trans hW.symm), fun w hw => ?_⟩
  rw [LinearIsometry.toLinearIsometryEquiv_apply, hf]
  obtain ⟨c, rfl⟩ := hWspan w
  have hc : |c| = 1 := by
    have := norm_eq_one_of_line hW hw
    rwa [norm_smul, hw0n, mul_one, Real.norm_eq_abs] at this
  rcases (abs_eq zero_le_one).1 hc with rfl | rfl
  · rw [one_smul, hφv, one_smul]
  · rw [neg_one_smul, hodd w0 hw0, map_neg, hφv, neg_one_smul]

end Sol_Plasticity_C0Sum_isometryOn_of_reduced

open Sol_Plasticity_C0Sum_isometryOn_of_reduced in
theorem solution {ι κ : Type*}
    (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (E' : κ → Type*) [∀ k, NormedAddCommGroup (E' k)] [∀ k, NormedSpace ℝ (E' k)]
    (hE : ∀ i, Module.finrank ℝ (E i) = 1 ∨ (Module.finrank ℝ (E i) = 2 ∧
      4 < (Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1)).encard))
    (hE' : ∀ k, Module.finrank ℝ (E' k) = 1 ∨ (Module.finrank ℝ (E' k) = 2 ∧
      4 < (Set.extremePoints ℝ (Metric.closedBall (0 : E' k) 1)).encard))
    (F : c0Sum E → c0Sum E')
    (hbij : Set.BijOn F (Metric.closedBall 0 1) (Metric.closedBall 0 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall 0 1)) :
    ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, ∀ y ∈ Metric.closedBall (0 : c0Sum E) 1,
      ‖F x - F y‖ = ‖x - y‖ := by
  obtain ⟨σ, hσ, hnorm⟩ := Plasticity.C0Sum.exists_blockEquiv E E' hE hE' F hbij hlip
  have hE'' : ∀ k, Module.finrank ℝ (E' k) = 1 ∨ Module.finrank ℝ (E' k) = 2 :=
    fun k => (hE' k).imp id And.left
  have hL : ∀ i, ∃ L : E i ≃ₗᵢ[ℝ] E' (σ i), ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1,
      (F x : lp E' ⊤) (σ i) ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E' (σ i)) 1) →
        L ((x : lp E ⊤) i) = (F x : lp E' ⊤) (σ i) := by
    intro i
    obtain ⟨g, hgext, hgodd, hgx, hgrad⟩ :=
      Plasticity.C0Sum.exists_extremeRule E E' hE hE'' F hbij hlip σ hnorm i
    have hLg : ∃ L : E i ≃ₗᵢ[ℝ] E' (σ i),
        ∀ w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : E' (σ i)) 1), L (g w) = w := by
      rcases hE i with h1 | ⟨h2, -⟩
      · exact exists_linearIsometryEquiv_of_line h1 ((hσ i).trans h1) g hgext hgodd
      · exact Plasticity.Plane.exists_linearIsometryEquiv_of_radial_le h2 ((hσ i).trans h2) g
          hgext hgrad
    obtain ⟨L, hL⟩ := hLg
    refine ⟨L, fun x hx hw => ?_⟩
    rw [hgx x hx hw]
    exact hL _ hw
  choose L hL using hL
  exact Plasticity.C0Sum.isometryOn_of_extreme_eq E E' hE F hbij hlip σ L hnorm
    (fun x hx i hw => hL i x hx hw)
