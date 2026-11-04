-- Prove2me | solution 1 for StrictCQ.CAKKT.tangentCone_subset_linCone
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T00:43:23.567138+00:00
-- url     : https://prove2.me/submissions/c3137143-464c-447d-9b6b-4b051c136d0c

import Mathlib
import Definitions.Def_StrictCQ_CAKKT_Setting

open Filter Topology
open scoped InnerProductSpace
open StrictCQ.CAKKT

lemma cakkt_dirlim {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 1 f)
    {xs d : EuclideanSpace ℝ (Fin n)} {t : ℕ → ℝ} {dk : ℕ → EuclideanSpace ℝ (Fin n)}
    (ht : ∀ k, 0 < t k) (ht0 : Tendsto t atTop (𝓝 0)) (hd : Tendsto dk atTop (𝓝 d)) :
    Tendsto (fun k => (t k)⁻¹ * (f (xs + t k • dk k) - f xs)) atTop
      (𝓝 ⟪gradient f xs, d⟫_ℝ) := by
  have hdiff : DifferentiableAt ℝ f xs := (hf.differentiable one_ne_zero) xs
  have hdl : Tendsto (fun k => t k • dk k) atTop (𝓝 0) := by
    have h2 : Tendsto (fun k => t k • dk k) atTop (𝓝 ((0:ℝ) • d)) := ht0.smul hd
    simpa using h2
  have hcd : Tendsto (fun k => (t k)⁻¹ • (t k • dk k)) atTop (𝓝 d) := by
    refine hd.congr' (Eventually.of_forall fun k => ?_)
    simp [smul_smul, inv_mul_cancel₀ (ht k).ne']
  have h := (hdiff.hasFDerivAt.hasFDerivWithinAt (s := Set.univ)).lim hdl
    (Eventually.of_forall fun _ => Set.mem_univ _) hcd
  have he : ⟪gradient f xs, d⟫_ℝ = fderiv ℝ f xs d := by
    simp [gradient, InnerProductSpace.toDual_symm_apply]
  rw [he]
  simpa [smul_eq_mul] using h

theorem solution {n m p : ℕ} (C : Constraints n m p) (hC : C.IsC1)
    {xs : EuclideanSpace ℝ (Fin n)} (hxs : xs ∈ C.feasible) :
    tangentCone C.feasible xs ⊆ C.linCone xs := by
  rintro d ⟨t, dk, ht, ht0, hd, hS⟩
  refine ⟨fun i => ?_, fun j hj => ?_⟩
  · have h := cakkt_dirlim (hC.1 i) (xs := xs) ht ht0 hd
    have h0 : (fun k => (t k)⁻¹ * (C.h i (xs + t k • dk k) - C.h i xs)) = fun _ => 0 := by
      funext k; simp [(hS k).1 i, hxs.1 i]
    rw [h0] at h
    exact (tendsto_nhds_unique h tendsto_const_nhds)
  · have h := cakkt_dirlim (hC.2 j) (xs := xs) ht ht0 hd
    refine le_of_tendsto' h fun k => ?_
    rw [hj, sub_zero]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_pos.2 (ht k)).le ((hS k).2 j)
