-- Prove2me | solution 1 for SamplingPiecewiseGeodesic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:58:57.828532+00:00
-- url     : https://prove2.me/submissions/0eb560d0-cd95-493f-9346-1982d3e81611

import Definitions.Def_Tablet_curveSampling
import Definitions.Def_Tablet_IsPiecewiseGeodesic
import Definitions.Def_Tablet_GeodesicIsPiecewiseGeodesic
import Definitions.Def_Tablet_ConcatPiecewiseGeodesic
import Definitions.Def_Tablet_SamplingPiecewiseGeodesic
import Theorems.Thm_ConcatPiecewiseGeodesic
import Theorems.Thm_GeodesicIsPiecewiseGeodesic


set_option autoImplicit false
open Set
theorem _root_.solution {E : Type*} [MetricSpace E] (GP : GeodesicPairing E)
    (γ : Curve E) (δ : ℝ) (hδ0 : 0 < δ) (hδlen : δ < γ.len) :
    IsPiecewiseGeodesic (curveSampling GP γ δ hδ0 hδlen) := by
-- BODY
  unfold curveSampling
  generalize (⌈γ.len / δ⌉₊ - 1) = n
  induction n with
  | zero => exact ⟨1, GeodesicIsPiecewiseGeodesic GP _ _⟩
  | succ k ih =>
      obtain ⟨m, hm⟩ := ih
      refine ⟨m + 1, ?_⟩
      apply ConcatPiecewiseGeodesic _ _ ?_ m 1 hm (GeodesicIsPiecewiseGeodesic GP _ _)
      rw [GP.start_eq]
      exact @Subtype.prop _
        (fun c : Curve E => c.toFun c.len = γ.toFun (min (((k + 1 : ℕ) : ℝ) * δ) γ.len)) _
