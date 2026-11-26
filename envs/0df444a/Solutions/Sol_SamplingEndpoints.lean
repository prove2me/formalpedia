-- Prove2me | solution 1 for SamplingEndpoints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:56:12.734849+00:00
-- url     : https://prove2.me/submissions/f63e2402-7e58-4cb0-b2cd-a29b6793aa5e

import Definitions.Def_Tablet_curveSampling
import Definitions.Def_Tablet_SamplingEndpoints

set_option autoImplicit false
open Set
theorem _root_.solution {E : Type*} [MetricSpace E] (GP : GeodesicPairing E)
    (γ : Curve E) (δ : ℝ) (hδ0 : 0 < δ) (hδlen : δ < γ.len) :
    (curveSampling GP γ δ hδ0 hδlen).toFun 0 = γ.toFun 0 ∧
      (curveSampling GP γ δ hδ0 hδlen).toFun (curveSampling GP γ δ hδ0 hδlen).len
        = γ.toFun γ.len := by
-- BODY
  have concat_start : ∀ (a b : Curve E) (h : a.toFun a.len = b.toFun 0),
      (curveConcat a b h).toFun 0 = a.toFun 0 := by
    intro a b h
    show (if (0:ℝ) ≤ a.len then a.toFun 0 else b.toFun (0 - a.len)) = a.toFun 0
    rw [if_pos a.len_nonneg]
  have hlen0 : 0 < γ.len := lt_trans hδ0 hδlen
  have hceil : 0 < ⌈γ.len / δ⌉₊ := Nat.ceil_pos.mpr (div_pos hlen0 hδ0)
  have hsub : (⌈γ.len / δ⌉₊ - 1) + 1 = ⌈γ.len / δ⌉₊ := Nat.succ_pred_eq_of_pos hceil
  have hge : γ.len ≤ (⌈γ.len / δ⌉₊ : ℝ) * δ := by
    have := Nat.le_ceil (γ.len / δ)
    rwa [div_le_iff₀ hδ0] at this
  constructor
  · unfold curveSampling
    generalize (⌈γ.len / δ⌉₊ - 1) = n
    induction n with
    | zero =>
        show (GP.G _ _).toFun 0 = γ.toFun 0
        rw [GP.start_eq]
        norm_num [γ.len_nonneg]
    | succ k ih =>
        refine (concat_start _ _ ?_).trans ih
        rw [GP.start_eq]
        exact @Subtype.prop _
          (fun c : Curve E => c.toFun c.len = γ.toFun (min (((k + 1 : ℕ) : ℝ) * δ) γ.len)) _
  · unfold curveSampling
    refine Eq.trans (@Subtype.prop _
      (fun c : Curve E => c.toFun c.len
          = γ.toFun (min (((⌈γ.len / δ⌉₊ - 1 + 1 : ℕ) : ℝ) * δ) γ.len)) _) ?_
    congr 1
    rw [hsub]
    exact min_eq_right hge
