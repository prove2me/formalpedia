-- Prove2me | solution 1 for RoughSurfaceScattering.near_field_data_continuation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:42:51.845855+00:00
-- url     : https://prove2.me/submissions/9b870bb6-e3ff-4563-8f40-e6831c5915ec
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic
import Theorems.Thm_RoughSurfaceScattering_scattered_field_continuation
import Theorems.Thm_RoughSurfaceScattering_scattered_field_reciprocity

open MeasureTheory
open RoughSurfaceScattering

/-- The measurement segment lies above the interface. -/
lemma measSeg_subset_Dplus (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f) (c d : ℝ) (hc : fsup f < c) :
    measSeg c d ⊆ Dplus f := by
  intro x hx
  obtain ⟨C, hC⟩ := hf.2.2.1
  have hbdd : BddAbove (Set.range f) := ⟨C, by rintro _ ⟨t, rfl⟩; exact (abs_le.mp (hC t)).2⟩
  have hle : f (x 0) ≤ fsup f := le_ciSup hbdd (x 0)
  show f (x 0) < x 1
  rw [hx.1]
  linarith

theorem solution (f1 f2 : ℝ → ℝ) (hf1 : IsBC1Alpha 1 f1) (hf2 : IsBC1Alpha 1 f2)
    (kp k1 k2 μ1 μ2 : ℝ) (hpar1 : ParamCond kp k1 μ1) (hpar2 : ParamCond kp k2 μ2)
    (c d : ℝ) (hd : 0 < d) (hc1 : fsup f1 < c) (hc2 : fsup f2 < c)
    (U1 U2 : R2 → (R2 → ℂ) × (R2 → ℂ))
    (hU1 : ∀ y ∈ Dplus f1, IsTSPSolution f1 kp k1 μ1 (incData f1 (pointSource kp y)).1
      (incData f1 (pointSource kp y)).2 (U1 y).1 (U1 y).2)
    (hU2 : ∀ y ∈ Dplus f2, IsTSPSolution f2 kp k2 μ2 (incData f2 (pointSource kp y)).1
      (incData f2 (pointSource kp y)).2 (U2 y).1 (U2 y).2)
    (hdata : ∀ x ∈ measSeg c d, ∀ y ∈ measSeg c d, (U1 y).1 x = (U2 y).1 x) :
    ∀ x ∈ Dplus f1 ∩ Dplus f2, ∀ y ∈ Dplus f1 ∩ Dplus f2, (U1 y).1 x = (U2 y).1 x := by
  have hseg : ∀ z ∈ measSeg c d, z ∈ Dplus f1 ∩ Dplus f2 := fun z hz =>
    ⟨measSeg_subset_Dplus f1 hf1 c d hc1 hz, measSeg_subset_Dplus f2 hf2 c d hc2 hz⟩
  -- continuation of the data for sources on the segment
  have hcont : ∀ y ∈ Dplus f1 ∩ Dplus f2,
      (∀ z ∈ measSeg c d, (U1 y).1 z = (U2 y).1 z) →
      ∀ x ∈ Dplus f1 ∩ Dplus f2, (U1 y).1 x = (U2 y).1 x := fun y hy h =>
    scattered_field_continuation f1 f2 hf1 hf2 kp k1 k2 μ1 μ2 hpar1 hpar2 y hy
      (U1 y).1 (U1 y).2 (U2 y).1 (U2 y).2 (hU1 y hy.1) (hU2 y hy.2) c d hd hc1 hc2 h
  have step1 : ∀ z ∈ measSeg c d, ∀ x ∈ Dplus f1 ∩ Dplus f2, (U1 z).1 x = (U2 z).1 x :=
    fun z hz => hcont z (hseg z hz) (fun w hw => hdata w hw z hz)
  have hrec1 := scattered_field_reciprocity f1 hf1 kp k1 μ1 hpar1 U1 hU1
  have hrec2 := scattered_field_reciprocity f2 hf2 kp k2 μ2 hpar2 U2 hU2
  -- by reciprocity, the data on the segment are also known for every source in `D₁⁺ ∩ D₂⁺`
  intro x hx y hy
  refine hcont y hy (fun z hz => ?_) x hx
  calc (U1 y).1 z = (U1 z).1 y := hrec1 z (hseg z hz).1 y hy.1
    _ = (U2 z).1 y := step1 z hz y hy
    _ = (U2 y).1 z := (hrec2 z (hseg z hz).2 y hy.2).symm
