-- Prove2me | solution 1 for Plasticity.BallMap.map_smul_of_map_mem_extremePoints
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-14T19:07:00.057914+00:00
-- url     : https://prove2.me/submissions/2d5b700f-1590-403d-943b-29a247ba1e84

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Module
import Theorems.Thm_Plasticity_BallMap_map_zero_of_surjOn
import Theorems.Thm_Plasticity_BallMap_map_neg_of_map_mem_extremePoints

/-!
# A nonexpansive bijection of unit balls is linear on segments through preimages of extreme
points

Cf. Cascales–Kadets–Orihuela–Wingler, RACSAM 2016, Theorem 2.3; Zavarzina, arXiv:1704.06961,
Theorem 2.3. Split from the proof of U01; uses `Plasticity.BallMap.map_zero_of_surjOn` and
`Plasticity.BallMap.map_neg_of_map_mem_extremePoints`.
-/

namespace Sol_Plasticity_BallMap_map_smul_of_map_mem_extremePoints

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

lemma midExt_neg {Y : Type*} [NormedAddCommGroup Y] {e : Y} (he : MidExt e) :
    MidExt (-e) := by
  intro z h1 h2
  apply he z
  · have h : e + z = -(-e - z) := by abel
    rw [h, norm_neg]; exact h2
  · have h : e - z = -(-e + z) := by abel
    rw [h, norm_neg]; exact h1

/-- Homogeneity along a ray ending at a midpoint-extreme value. -/
lemma ray {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {F : X → Y}
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1)) (hF0 : F 0 = 0)
    {x : X} (hx : ‖x‖ ≤ 1) (he1 : ‖F x‖ ≤ 1) (he : MidExt (F x))
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : F (t • x) = t • F x := by
  have hxB : x ∈ Metric.closedBall (0 : X) 1 := by simpa using hx
  have htx : ‖t • x‖ ≤ t := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    nlinarith [norm_nonneg x]
  have htxB : t • x ∈ Metric.closedBall (0 : X) 1 := by simpa using htx.trans ht1
  have h0B : (0 : X) ∈ Metric.closedBall (0 : X) 1 := by simp
  have hw : ‖F (t • x)‖ ≤ t := by
    have h := lip_norm hlip htxB h0B
    rw [hF0, sub_zero, sub_zero] at h
    linarith
  have hew : ‖F x - F (t • x)‖ ≤ 1 - t := by
    have h := lip_norm hlip hxB htxB
    have h2 : x - t • x = (1 - t) • x := by rw [sub_smul, one_smul]
    rw [h2, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)] at h
    nlinarith [norm_nonneg x]
  set e := F x with he_def
  set w := F (t • x) with hw_def
  have key := he (w - t • e) ?_ ?_
  · exact sub_eq_zero.mp key
  · have h : e + (w - t • e) = (1 - t) • e + w := by module
    rw [h]
    calc ‖(1 - t) • e + w‖ ≤ ‖(1 - t) • e‖ + ‖w‖ := norm_add_le _ _
      _ = (1 - t) * ‖e‖ + ‖w‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      _ ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_left he1 (sub_nonneg.mpr ht1)]
  · have h : e - (w - t • e) = t • e + (e - w) := by module
    rw [h]
    calc ‖t • e + (e - w)‖ ≤ ‖t • e‖ + ‖e - w‖ := norm_add_le _ _
      _ = t * ‖e‖ + ‖e - w‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
      _ ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_left he1 ht0]

end Sol_Plasticity_BallMap_map_smul_of_map_mem_extremePoints

open Sol_Plasticity_BallMap_map_smul_of_map_mem_extremePoints in
theorem solution {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (F : X → Y)
    (hbij : Set.BijOn F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (x : X) (hx : x ∈ Metric.closedBall (0 : X) 1)
    (hext : F x ∈ (Metric.closedBall (0 : Y) 1).extremePoints ℝ)
    (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    F (t • x) = t • F x := by
  have hF0 : F 0 = 0 := Plasticity.BallMap.map_zero_of_surjOn F hbij.surjOn hlip
  have hanti : F (-x) = -F x :=
    Plasticity.BallMap.map_neg_of_map_mem_extremePoints F hbij hlip x hx hext
  have hP : MidExt (F x) := midExt_of_mem hext
  have hx1 : ‖x‖ ≤ 1 := by simpa using hx
  have hFx1 : ‖F x‖ ≤ 1 := by simpa using hbij.mapsTo hx
  have hP' : MidExt (F (-x)) := by rw [hanti]; exact midExt_neg hP
  have hFnx1 : ‖F (-x)‖ ≤ 1 := by rw [hanti, norm_neg]; exact hFx1
  have hnx1 : ‖-x‖ ≤ 1 := by rw [norm_neg]; exact hx1
  obtain ⟨ht1, ht2⟩ := ht
  -- `t ≥ 0`: the ray to `x`; `t ≤ 0`: the ray to `-x`, whose image `-F x` is extreme too
  rcases le_total 0 t with ht | ht
  · exact ray hlip hF0 hx1 hFx1 hP ht ht2
  · have h := ray hlip hF0 hnx1 hFnx1 hP' (t := -t) (by linarith) (by linarith)
    simpa [hanti] using h
