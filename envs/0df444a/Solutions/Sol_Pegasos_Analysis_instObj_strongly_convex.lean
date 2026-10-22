-- Prove2me | solution 1 for Pegasos.Analysis.instObj_strongly_convex
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:36:28.530838+00:00
-- url     : https://prove2.me/submissions/af345c4c-e593-44f7-92f8-8e660cd1c35f

import Mathlib
import Definitions.Def_Pegasos_Analysis_Model

set_option autoImplicit false

open Pegasos.Analysis
open scoped InnerProductSpace

namespace PEGAux

lemma quad_ineq {n : ℕ} (lam : ℝ) (hlam : 0 ≤ lam) (u w : EuclideanSpace ℝ (Fin n)) :
    lam / 2 * ‖w‖ ^ 2 + lam * inner ℝ (u - w) w ≤ lam / 2 * ‖u‖ ^ 2 := by
  have h := norm_add_sq_real w (u - w)
  rw [add_sub_cancel] at h
  rw [h, real_inner_comm]
  nlinarith [mul_nonneg hlam (sq_nonneg ‖u - w‖)]

lemma hinge_sub {n : ℕ} (w u x : EuclideanSpace ℝ (Fin n)) (y : ℝ) :
    UnderstandingML.hingeLoss w (x, y)
      + (if y * inner ℝ w x < 1 then -(y * inner ℝ (u - w) x) else 0)
      ≤ UnderstandingML.hingeLoss u (x, y) := by
  unfold UnderstandingML.hingeLoss
  simp only
  split_ifs with h
  · rw [max_eq_right (by linarith), inner_sub_left]
    have := le_max_right 0 (1 - y * inner ℝ u x)
    linarith
  · rw [max_eq_left (by linarith)]
    simp

lemma hinge_nonneg {n : ℕ} (w x : EuclideanSpace ℝ (Fin n)) (y : ℝ) :
    0 ≤ UnderstandingML.hingeLoss w (x, y) := by
  unfold UnderstandingML.hingeLoss
  exact le_max_left _ _

lemma le_of_small (A C D : ℝ) (h : ∀ s : ℝ, 0 < s → s ≤ 1 → A ≤ C + s * D) : A ≤ C := by
  have ht : Filter.Tendsto (fun s : ℝ => C + s * D) (nhdsWithin 0 (Set.Ioi 0)) (nhds C) := by
    have : Filter.Tendsto (fun s : ℝ => C + s * D) (nhds 0) (nhds (C + 0 * D)) :=
      (continuous_const.add (continuous_id.mul continuous_const)).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
  exact h s hs.1 hs.2.le

lemma strong_sub {n : ℕ} (lam : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ (fun v => f v - lam / 2 * ‖v‖ ^ 2))
    (w g : EuclideanSpace ℝ (Fin n)) (hg : UnderstandingML.IsSubgradient f w g)
    (u : EuclideanSpace ℝ (Fin n)) :
    f w - f u + lam / 2 * ‖w - u‖ ^ 2 ≤ inner ℝ (w - u) g := by
  have hnorm : ‖u‖ ^ 2 = ‖w‖ ^ 2 + 2 * inner ℝ w (u - w) + ‖u - w‖ ^ 2 := by
    have := norm_add_sq_real w (u - w)
    rwa [add_sub_cancel] at this
  have key : ∀ s : ℝ, 0 < s → s ≤ 1 →
      (inner ℝ (u - w) g - lam * inner ℝ w (u - w) - (f u - lam / 2 * ‖u‖ ^ 2)
        + (f w - lam / 2 * ‖w‖ ^ 2)) ≤ 0 + s * (lam / 2 * ‖u - w‖ ^ 2) := by
    intro s hs0 hs1
    have hc := hf.2 (Set.mem_univ w) (Set.mem_univ u) (show 0 ≤ 1 - s by linarith) hs0.le
      (by ring)
    simp only [smul_eq_mul] at hc
    have hp : (1 - s) • w + s • u = w + s • (u - w) := by module
    have hg' := hg ((1 - s) • w + s • u)
    have hpw : (1 - s) • w + s • u - w = s • (u - w) := by module
    rw [hpw, inner_smul_left] at hg'
    simp only [conj_trivial] at hg'
    rw [hp] at hc
    have h3 := norm_add_sq_real w (s • (u - w))
    rw [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h3
    rw [hp] at hg'
    have h4 : s * (inner ℝ (u - w) g - lam * inner ℝ w (u - w) - (f u - lam / 2 * ‖u‖ ^ 2)
        + (f w - lam / 2 * ‖w‖ ^ 2)) ≤ s * (0 + s * (lam / 2 * ‖u - w‖ ^ 2)) := by
      rw [h3] at hc
      nlinarith [hc, hg']
    exact le_of_mul_le_mul_left h4 hs0
  have hA := le_of_small _ _ _ key
  have e1 : ‖w - u‖ = ‖u - w‖ := norm_sub_rev w u
  have e2 : inner ℝ (w - u) g = - inner ℝ (u - w) g := by
    rw [← inner_neg_left, neg_sub]
  have h5 : lam / 2 * ‖u‖ ^ 2
      = lam / 2 * (‖w‖ ^ 2 + 2 * inner ℝ w (u - w) + ‖u - w‖ ^ 2) := by rw [hnorm]
  rw [e1, e2]
  linarith [hA, h5]

end PEGAux

open PEGAux

lemma hinge_convex {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (y : ℝ) (u v : EuclideanSpace ℝ (Fin n))
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    UnderstandingML.hingeLoss (a • u + b • v) (x, y) ≤
      a * UnderstandingML.hingeLoss u (x, y) + b * UnderstandingML.hingeLoss v (x, y) := by
  unfold UnderstandingML.hingeLoss
  simp only
  apply max_le
  · have h1 := le_max_left 0 (1 - y * inner ℝ u x)
    have h2 := le_max_left 0 (1 - y * inner ℝ v x)
    nlinarith [mul_nonneg ha h1, mul_nonneg hb h2]
  · have h1 := le_max_right 0 (1 - y * inner ℝ u x)
    have h2 := le_max_right 0 (1 - y * inner ℝ v x)
    rw [inner_add_left, inner_smul_left, inner_smul_left]
    simp only [conj_trivial]
    have e : 1 - y * (a * inner ℝ u x + b * inner ℝ v x)
        = a * (1 - y * inner ℝ u x) + b * (1 - y * inner ℝ v x) := by
      have : (1 : ℝ) = a + b := hab.symm
      calc 1 - y * (a * inner ℝ u x + b * inner ℝ v x)
          = (a + b) * 1 - y * (a * inner ℝ u x + b * inner ℝ v x) := by rw [← this]; ring
        _ = _ := by ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

theorem solution {n m k : ℕ} (lam : ℝ)
    (x : Fin m → EuclideanSpace ℝ (Fin n)) (y : Fin m → ℝ) (B : Fin k → Fin m) :
    ConvexOn ℝ Set.univ (fun w => instObj lam x y B w - lam / 2 * ‖w‖ ^ 2) := by
  refine ⟨convex_univ, ?_⟩
  intro u _ v _ a b ha hb hab
  simp only [instObj, smul_eq_mul]
  have hk : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
  have hsum : ∑ j, UnderstandingML.hingeLoss (a • u + b • v) (x (B j), y (B j)) ≤
      a * ∑ j, UnderstandingML.hingeLoss u (x (B j), y (B j))
        + b * ∑ j, UnderstandingML.hingeLoss v (x (B j), y (B j)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun j _ => hinge_convex _ _ u v a b ha hb hab)
  have := mul_le_mul_of_nonneg_left hsum hk
  nlinarith
