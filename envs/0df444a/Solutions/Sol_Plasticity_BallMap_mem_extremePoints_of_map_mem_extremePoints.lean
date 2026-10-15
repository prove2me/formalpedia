-- Prove2me | solution 1 for Plasticity.BallMap.mem_extremePoints_of_map_mem_extremePoints
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-14T19:06:17.992528+00:00
-- url     : https://prove2.me/submissions/efa8965a-91d4-4e6b-ad52-9e74f76bc2a4

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Module
import Theorems.Thm_Plasticity_BallMap_map_zero_of_surjOn
import Theorems.Thm_Plasticity_BallMap_map_neg_of_map_mem_extremePoints

/-!
# A nonexpansive bijection of unit balls pulls extreme points back to extreme points

Cf. Cascales–Kadets–Orihuela–Wingler, RACSAM 2016, Theorem 2.3; Zavarzina, arXiv:1704.06961,
Theorem 2.3. Split from the proof of U01; uses `Plasticity.BallMap.map_zero_of_surjOn` and
`Plasticity.BallMap.map_neg_of_map_mem_extremePoints`.
-/

namespace Sol_Plasticity_BallMap_mem_extremePoints_of_map_mem_extremePoints

/-- A `1`-Lipschitz map on `s`, stated with norms. -/
lemma lip_norm {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y] {F : X → Y}
    {s : Set X} (hlip : LipschitzOnWith 1 F s) {x y : X} (hx : x ∈ s) (hy : y ∈ s) :
    ‖F x - F y‖ ≤ ‖x - y‖ := by
  have h := hlip.dist_le_mul x hx y hy
  simpa [dist_eq_norm] using h

/-- Midpoint form of extremality in the closed unit ball: `e ± z` both in the ball forces
`z = 0`. -/
def MidExt {Y : Type*} [NormedAddCommGroup Y] (e : Y) : Prop :=
  ∀ z : Y, ‖e + z‖ ≤ 1 → ‖e - z‖ ≤ 1 → z = 0

lemma midExt_of_mem {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {e : Y}
    (he : e ∈ (Metric.closedBall (0 : Y) 1).extremePoints ℝ) : MidExt e := by
  intro z h1 h2
  have : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  have hseg : e ∈ openSegment ℝ (e + z) (e - z) := mem_openSegment_add_sub e z
  have hm1 : e + z ∈ Metric.closedBall (0 : Y) 1 := by simpa using h1
  have hm2 : e - z ∈ Metric.closedBall (0 : Y) 1 := by simpa using h2
  have h := he.2 hm1 hm2 hseg
  simpa using h

end Sol_Plasticity_BallMap_mem_extremePoints_of_map_mem_extremePoints

open Sol_Plasticity_BallMap_mem_extremePoints_of_map_mem_extremePoints in
theorem solution {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (F : X → Y)
    (hbij : Set.BijOn F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (x : X) (hx : x ∈ Metric.closedBall (0 : X) 1)
    (hext : F x ∈ (Metric.closedBall (0 : Y) 1).extremePoints ℝ) :
    x ∈ (Metric.closedBall (0 : X) 1).extremePoints ℝ := by
  have h0mem : (0 : X) ∈ Metric.closedBall (0 : X) 1 := by simp
  have hball : ∀ x ∈ Metric.closedBall (0 : X) 1, ‖x‖ ≤ 1 := fun x hx => by simpa using hx
  have hF0 : F 0 = 0 := Plasticity.BallMap.map_zero_of_surjOn F hbij.surjOn hlip
  have hanti : F (-x) = -F x :=
    Plasticity.BallMap.map_neg_of_map_mem_extremePoints F hbij hlip x hx hext
  have hP : MidExt (F x) := midExt_of_mem hext
  have hnegB : -x ∈ Metric.closedBall (0 : X) 1 := by simpa using hball x hx
  refine ⟨hx, ?_⟩
  intro x₁ hx₁ x₂ hx₂ hseg
  obtain ⟨a, b, ha, hb, hab, hx_eq⟩ := hseg
  have hab4 : a * b ≤ 1 / 4 := by nlinarith [sq_nonneg (a - b)]
  have habpos : 0 < a * b := mul_pos ha hb
  -- `z = ab (x₁ - x₂)` with `x ± z` in the ball; then `F z = 0`
  set z : X := (a * b) • (x₁ - x₂) with hz
  have hpz : x + z ∈ Metric.closedBall (0 : X) 1 := by
    have h : x + z = (a + a * b) • x₁ + (b - a * b) • x₂ := by
      rw [← hx_eq]; simp only [z]; module
    rw [h]
    exact convex_closedBall (0 : X) 1 hx₁ hx₂ (by positivity) (by nlinarith) (by linarith)
  have hmz : x - z ∈ Metric.closedBall (0 : X) 1 := by
    have h : x - z = (a - a * b) • x₁ + (b + a * b) • x₂ := by
      rw [← hx_eq]; simp only [z]; module
    rw [h]
    exact convex_closedBall (0 : X) 1 hx₁ hx₂ (by nlinarith) (by positivity) (by linarith)
  have hzB : z ∈ Metric.closedBall (0 : X) 1 := by
    rw [mem_closedBall_zero_iff, hz, norm_smul, Real.norm_eq_abs, abs_of_pos habpos]
    have := norm_sub_le x₁ x₂
    have := hball x₁ hx₁
    have := hball x₂ hx₂
    nlinarith
  have hFz : F z = 0 := by
    apply hP (F z)
    · have h := lip_norm hlip hzB hnegB
      rw [hanti, sub_neg_eq_add, sub_neg_eq_add, add_comm (F z), add_comm z] at h
      linarith [hball _ hpz]
    · have h := lip_norm hlip hx hzB
      linarith [hball _ hmz]
  -- injectivity: `z = 0`, so `x₁ = x₂ = x`
  have hz0 : z = 0 := hbij.injOn hzB h0mem (hFz.trans hF0.symm)
  have hx12 : x₁ = x₂ := by
    have h := (smul_eq_zero.mp hz0).resolve_left habpos.ne'
    exact sub_eq_zero.mp h
  subst hx12
  rw [← hx_eq, ← add_smul, hab, one_smul]
