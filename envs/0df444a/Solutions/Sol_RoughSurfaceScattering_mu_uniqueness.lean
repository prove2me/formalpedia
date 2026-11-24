-- Prove2me | solution 1 for RoughSurfaceScattering.mu_uniqueness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T03:53:38.75021+00:00
-- url     : https://prove2.me/submissions/88426ed3-997a-47e4-b190-87487b06357b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic
import Theorems.Thm_RoughSurfaceScattering_mu_itp_bound
import Theorems.Thm_RoughSurfaceScattering_h1Norm_sub_le
import Theorems.Thm_RoughSurfaceScattering_laplace_h1_blowup
import Theorems.Thm_RoughSurfaceScattering_point_source_singularity

open MeasureTheory
open RoughSurfaceScattering

/-- `x ↦ Φ₀(x,z)` is `C¹` away from the source point. -/
lemma phi0_contDiffOn (z : R2) :
    ContDiffOn ℝ 1 (fun x' : R2 => Phi 0 x' z) {x | x ≠ z} := by
  intro x hx
  have hx' : x - z ≠ 0 := sub_ne_zero.mpr hx
  have hn : ContDiffAt ℝ 1 (fun x' : R2 => ‖x' - z‖) x :=
    (contDiffAt_norm ℝ hx').comp x ((contDiffAt_id).sub contDiffAt_const)
  have hpos : 0 < ‖x - z‖ := norm_pos_iff.mpr hx'
  have hinv : ContDiffAt ℝ 1 (fun x' : R2 => 1 / ‖x' - z‖) x := by
    have := (contDiffAt_inv ℝ hpos.ne').comp x hn
    simpa [one_div, Function.comp_def] using this
  have hlog : ContDiffAt ℝ 1 (fun x' : R2 => Real.log (1 / ‖x' - z‖)) x :=
    (Real.contDiffAt_log.mpr (by positivity)).comp x hinv
  have hreal : ContDiffAt ℝ 1
      (fun x' : R2 => 1 / (2 * Real.pi) * Real.log (1 / ‖x' - z‖)) x :=
    contDiffAt_const.mul hlog
  have hc : ContDiffAt ℝ 1
      (fun x' : R2 => ((1 / (2 * Real.pi) * Real.log (1 / ‖x' - z‖) : ℝ) : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hreal
  simpa [Phi] using hc.contDiffWithinAt

theorem solution (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f)
    (lam : ℝ) (hlam : 0 < lam ∧ lam ≤ 1) (hf' : IsC2Lambda lam f)
    (kp k1 k2 μ1 μ2 : ℝ) (hpar1 : ParamCond kp k1 μ1) (hpar2 : ParamCond kp k2 μ2)
    (U1 U2 : R2 → (R2 → ℂ) × (R2 → ℂ))
    (hU1 : ∀ y ∈ Dplus f, IsTSPSolution f kp k1 μ1 (incData f (pointSource kp y)).1
      (incData f (pointSource kp y)).2 (U1 y).1 (U1 y).2)
    (hU2 : ∀ y ∈ Dplus f, IsTSPSolution f kp k2 μ2 (incData f (pointSource kp y)).1
      (incData f (pointSource kp y)).2 (U2 y).1 (U2 y).2)
    (hagree : ∀ x ∈ Dplus f, ∀ y ∈ Dplus f, (U1 y).1 x = (U2 y).1 x) :
    μ1 = μ2 := by
  by_contra hμ
  -- thresholds from the interior transmission bound and from Theorem 5.2
  obtain ⟨δ1, hδ1, hITP⟩ := mu_itp_bound f hf lam hlam hf' kp k1 k2 μ1 μ2 hpar1 hpar2 hμ
    U1 U2 hU1 hU2 hagree 0
  obtain ⟨δ2, hδ2, h52⟩ := point_source_singularity f hf lam hlam.1 hlam.2 hf' kp k1 μ1 hpar1 0
  obtain ⟨δ, hδ, hδm⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < min δ1 δ2 :=
    ⟨min δ1 δ2 / 2, by have := lt_min hδ1 hδ2; linarith,
      by have := lt_min hδ1 hδ2; linarith⟩
  have hδ1' : δ < δ1 := lt_of_lt_of_le hδm (min_le_left _ _)
  have hδ2' : δ < δ2 := lt_of_lt_of_le hδm (min_le_right _ _)
  obtain ⟨hxj, h52'⟩ := h52 δ hδ hδ2'
  obtain ⟨D0, hD0, hsub, hsubD, C1, hC1⟩ := hITP δ hδ hδ1'
  -- Theorem 5.2 for the family `j ↦ U1 x_j` of point-source solutions
  let u : ℕ → (R2 → ℂ) × (R2 → ℂ) := fun j => U1 (gpt f 0 - (δ / (j : ℝ)) • normal f 0)
  obtain ⟨C2, hC2⟩ := h52' D0 hD0 hsub hsubD u (fun j hj => hU1 _ (hxj j hj))
  -- the blow-up of `(2/(μ₁+1)) Φ₀(·, x_j)` in `H¹(D₀)`
  have hμ1 : 0 < μ1 := hpar1.2.2.1
  have ha : (2 / (μ1 + 1) : ℝ) ≠ 0 := by positivity
  obtain ⟨j, hj, hblow⟩ := laplace_h1_blowup f hf 0 δ hδ D0 hsub (2 / (μ1 + 1)) ha
    (max C1 0 + max C2 0)
  -- regularity on `D₀`
  have hxjD : ∀ x ∈ D0, x ≠ gpt f 0 - (δ / (j : ℝ)) • normal f 0 := by
    intro x hx h
    have h1 := hsubD hx
    have h2 := hxj j hj
    rw [h] at h1
    simp only [Dplus, Dminus, Set.mem_setOf_eq] at h1 h2
    linarith
  have huc : ContDiffOn ℝ 1 (u j).2 D0 := by
    obtain ⟨_, _, _, _, _, _, _, hum, -⟩ := hU1 _ (hxj j hj)
    exact (hum.of_le (by norm_num)).mono hsubD
  have hphic : ContDiffOn ℝ 1
      (fun x => ((2 / (μ1 + 1) : ℝ) : ℂ) * Phi 0 x (gpt f 0 - (δ / (j : ℝ)) • normal f 0)) D0 :=
    contDiffOn_const.mul ((phi0_contDiffOn _).mono (fun x hx => hxjD x hx))
  have hwc : ContDiffOn ℝ 1 (fun x => (u j).2 x - ((2 / (μ1 + 1) : ℝ) : ℂ) *
      Phi 0 x (gpt f 0 - (δ / (j : ℝ)) • normal f 0)) D0 := huc.sub hphic
  -- triangle inequality in `H¹(D₀)`
  have htri := h1Norm_sub_le D0 hD0.1 (u j).2 _ huc hwc
  have heq : (fun x => (u j).2 x - ((u j).2 x - ((2 / (μ1 + 1) : ℝ) : ℂ) *
      Phi 0 x (gpt f 0 - (δ / (j : ℝ)) • normal f 0))) =
      (fun x => ((2 / (μ1 + 1) : ℝ) : ℂ) * Phi 0 x (gpt f 0 - (δ / (j : ℝ)) • normal f 0)) := by
    funext x
    ring
  rw [heq] at htri
  have hbound : h1Norm D0
      (fun x => ((2 / (μ1 + 1) : ℝ) : ℂ) * Phi 0 x (gpt f 0 - (δ / (j : ℝ)) • normal f 0)) ≤
      ENNReal.ofReal (max C1 0 + max C2 0) := by
    rw [ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]
    refine htri.trans (add_le_add ((hC1 j hj).trans ?_) ((hC2 j hj).trans ?_))
    · exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
    · exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
  exact absurd (hblow.trans_le hbound) (lt_irrefl _)
