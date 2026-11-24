-- Prove2me | solution 1 for RoughSurfaceScattering.scattered_field_continuation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:29:57.008176+00:00
-- url     : https://prove2.me/submissions/4898d1bc-b33f-4d90-9ce6-bf2432e73687
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic
import Theorems.Thm_RoughSurfaceScattering_helmholtz_line_identity
import Theorems.Thm_RoughSurfaceScattering_tsp_halfplane_uniqueness
import Theorems.Thm_RoughSurfaceScattering_helmholtz_unique_continuation

open MeasureTheory
open RoughSurfaceScattering

lemma le_fsup (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f) (t : ℝ) : f t ≤ fsup f := by
  obtain ⟨C, hC⟩ := hf.2.2.1
  exact le_ciSup ⟨C, by rintro _ ⟨s, rfl⟩; exact (abs_le.mp (hC s)).2⟩ t

lemma pt_apply0 (a b : ℝ) : (pt a b) 0 = a := by simp [pt]
lemma pt_apply1 (a b : ℝ) : (pt a b) 1 = b := by simp [pt]

lemma isOpen_Dplus (f : ℝ → ℝ) (hf : Continuous f) : IsOpen (Dplus f) := by
  unfold Dplus
  exact isOpen_lt (by fun_prop) (by fun_prop)

/-- The region above the graph of a continuous function is connected. -/
lemma isConnected_above (F : ℝ → ℝ) (hF : Continuous F) :
    IsConnected {x : R2 | F (x 0) < x 1} := by
  have himg : {x : R2 | F (x 0) < x 1} =
      (fun q : ℝ × ℝ => pt q.1 (F q.1 + q.2)) '' (Set.univ ×ˢ Set.Ioi 0) := by
    ext x
    constructor
    · intro hx
      refine ⟨(x 0, x 1 - F (x 0)), ⟨trivial, ?_⟩, ?_⟩
      · simp only [Set.mem_Ioi, sub_pos]; exact hx
      · ext i; fin_cases i <;> simp [pt]
    · rintro ⟨q, ⟨-, hq⟩, rfl⟩
      simp only [Set.mem_setOf_eq, pt_apply0, pt_apply1]
      simp only [Set.mem_Ioi] at hq
      linarith
  rw [himg]
  refine (isConnected_univ.prod isConnected_Ioi).image _ (Continuous.continuousOn ?_)
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  fin_cases i <;> simp <;> fun_prop

theorem solution (f1 f2 : ℝ → ℝ) (hf1 : IsBC1Alpha 1 f1)
    (hf2 : IsBC1Alpha 1 f2) (kp k1 k2 μ1 μ2 : ℝ) (hpar1 : ParamCond kp k1 μ1)
    (hpar2 : ParamCond kp k2 μ2) (y : R2) (hy : y ∈ Dplus f1 ∩ Dplus f2)
    (u1p u1m u2p u2m : R2 → ℂ)
    (hu1 : IsTSPSolution f1 kp k1 μ1 (incData f1 (pointSource kp y)).1
      (incData f1 (pointSource kp y)).2 u1p u1m)
    (hu2 : IsTSPSolution f2 kp k2 μ2 (incData f2 (pointSource kp y)).1
      (incData f2 (pointSource kp y)).2 u2p u2m)
    (c d : ℝ) (hd : 0 < d) (hc1 : fsup f1 < c) (hc2 : fsup f2 < c)
    (hseg : ∀ x ∈ measSeg c d, u1p x = u2p x) :
    ∀ x ∈ Dplus f1 ∩ Dplus f2, u1p x = u2p x := by
  set G := Dplus f1 ∩ Dplus f2 with hG
  have hGo : IsOpen G := (isOpen_Dplus f1 hf1.1.continuous).inter
    (isOpen_Dplus f2 hf2.1.continuous)
  have hGeq : G = {x : R2 | (fun s => max (f1 s) (f2 s)) (x 0) < x 1} := by
    ext x; simp [hG, Dplus, max_lt_iff]
  have hGc : IsConnected G := by
    rw [hGeq]; exact isConnected_above _ (hf1.1.continuous.max hf2.1.continuous)
  obtain ⟨_, _, _, _, _, _, hC1, -, -, -, hH1, -⟩ := id hu1
  obtain ⟨_, _, _, _, _, _, hC2, -, -, -, hH2, -⟩ := id hu2
  have hC1G : ContDiffOn ℝ 2 u1p G := hC1.mono Set.inter_subset_left
  have hC2G : ContDiffOn ℝ 2 u2p G := hC2.mono Set.inter_subset_right
  have hH1G : IsHelmholtzOn G kp u1p := fun x hx => hH1 x hx.1
  have hH2G : IsHelmholtzOn G kp u2p := fun x hx => hH2 x hx.2
  have hup : ∀ x : R2, c ≤ x 1 → x ∈ G := fun x hx =>
    ⟨lt_of_le_of_lt (le_fsup f1 hf1 _) (lt_of_lt_of_le hc1 hx),
      lt_of_le_of_lt (le_fsup f2 hf2 _) (lt_of_lt_of_le hc2 hx)⟩
  -- (1) the data extend from the segment to the whole line `Γ_c`
  have hline := helmholtz_line_identity kp G hGo u1p u2p hC1G hC2G hH1G hH2G c d hd
    (fun t => hup _ (by rw [pt_apply1])) hseg
  -- (2) uniqueness of the Dirichlet problem in the half plane above `Γ_c`
  have hhalf := tsp_halfplane_uniqueness f1 f2 hf1 hf2 kp k1 k2 μ1 μ2 hpar1 hpar2 _ _ _ _
    u1p u1m u2p u2m hu1 hu2 c hc1 hc2 hline
  -- (3) unique continuation into the connected set `D₁⁺ ∩ D₂⁺`
  refine helmholtz_unique_continuation kp G hGo hGc u1p u2p hC1G hC2G hH1G hH2G
    {x : R2 | c < x 1} (isOpen_lt continuous_const (by fun_prop)) ⟨pt 0 (c + 1), by
      simp only [Set.mem_setOf_eq, pt_apply1]; linarith⟩
    (fun x hx => hup x (le_of_lt hx)) (fun x hx => hhalf x (le_of_lt hx))
