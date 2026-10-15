-- Prove2me | solution 1 for Plasticity.BallMap.map_neg_of_map_mem_extremePoints
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-14T19:05:36.001095+00:00
-- url     : https://prove2.me/submissions/2013d466-c257-40fc-8b3a-b5b48e6b934f

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Module
import Theorems.Thm_Plasticity_BallMap_map_zero_of_surjOn

/-!
# A nonexpansive bijection of unit balls is odd at preimages of extreme points

Cf. Cascales–Kadets–Orihuela–Wingler, RACSAM 2016, Theorem 2.3; Zavarzina, arXiv:1704.06961,
Theorem 2.3. Split from the proof of U01; uses `Plasticity.BallMap.map_zero_of_surjOn`.
-/

namespace Sol_Plasticity_BallMap_map_neg_of_map_mem_extremePoints

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

end Sol_Plasticity_BallMap_map_neg_of_map_mem_extremePoints

open Sol_Plasticity_BallMap_map_neg_of_map_mem_extremePoints in
theorem solution {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (F : X → Y)
    (hbij : Set.BijOn F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (x : X) (hx : x ∈ Metric.closedBall (0 : X) 1)
    (hext : F x ∈ (Metric.closedBall (0 : Y) 1).extremePoints ℝ) :
    F (-x) = -F x := by
  have h0mem : (0 : X) ∈ Metric.closedBall (0 : X) 1 := by simp
  have hF0 : F 0 = 0 := Plasticity.BallMap.map_zero_of_surjOn F hbij.surjOn hlip
  have hP : MidExt (F x) := midExt_of_mem hext
  -- a preimage `x'` of `-F x`; the midpoint `m` of `x, x'` is mapped to `0`
  have hnegB : -F x ∈ Metric.closedBall (0 : Y) 1 := by
    have := hbij.mapsTo hx
    simpa using this
  obtain ⟨x', hx', hFx'⟩ := hbij.surjOn hnegB
  have hx1 : ‖x‖ ≤ 1 := by simpa using hx
  have hx'1 : ‖x'‖ ≤ 1 := by simpa using hx'
  set m : X := (2 : ℝ)⁻¹ • (x + x') with hm
  have hm1 : ‖x - m‖ ≤ 1 := by
    have h : x - m = (2 : ℝ)⁻¹ • (x - x') := by simp only [m]; module
    rw [h, norm_smul]
    have := norm_sub_le x x'
    norm_num
    linarith
  have hm2 : ‖m - x'‖ ≤ 1 := by
    have h : m - x' = (2 : ℝ)⁻¹ • (x - x') := by simp only [m]; module
    rw [h, norm_smul]
    have := norm_sub_le x x'
    norm_num
    linarith
  have hmB : m ∈ Metric.closedBall (0 : X) 1 := by
    rw [mem_closedBall_zero_iff, hm, norm_smul]
    have := norm_add_le x x'
    norm_num
    linarith
  have hz : F m = 0 := by
    apply hP (F m)
    · have h := lip_norm hlip hmB hx'
      rw [hFx', sub_neg_eq_add, add_comm] at h
      linarith
    · have h := lip_norm hlip hx hmB
      linarith
  -- injectivity: `m = 0`, so `x' = -x`
  have hm0 : m = 0 := hbij.injOn hmB h0mem (hz.trans hF0.symm)
  have hsum : x + x' = 0 := by
    have h : (2 : ℝ)⁻¹ • (x + x') = 0 := hm0
    exact (smul_eq_zero.mp h).resolve_left (by norm_num)
  have hx'eq : x' = -x := (neg_eq_of_add_eq_zero_right hsum).symm
  rw [← hx'eq, hFx']
