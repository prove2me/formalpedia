-- Prove2me | solution 1 for Plasticity.A01
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-14T07:55:25.484034+00:00
-- url     : https://prove2.me/submissions/c7ae1cc4-4df2-4b80-8574-0f3530704626

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.EMetricSpace.Lipschitz
import Theorems.Thm_Plasticity_A01_averaged_covers
import Theorems.Thm_Plasticity_Ext_UniformAsymptoticRegularity

theorem solution {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (H : X → X)
    (hmaps : Set.MapsTo H (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : X) 1))
    (hlip : LipschitzOnWith 1 H (Metric.closedBall (0 : X) 1))
    (halign : ∀ a ∈ Metric.sphere (0 : X) 1, ‖a + H a‖ = 2) :
    Set.EqOn H id (Metric.closedBall (0 : X) 1) := by
  set B := Metric.closedBall (0 : X) 1 with hB
  set α : ℝ := 1 / 8 with hα
  set P : X → X := fun z => (1 - α) • z + α • H z with hP
  -- The averaged map keeps unit vectors on the sphere: a norming functional of a + H a
  -- takes the value 1 at both a and H a.
  have hPa : ∀ a ∈ Metric.sphere (0 : X) 1, 1 - 0 ≤ ‖(1 - α) • a + α • H a‖ := by
    intro a ha
    have ha1 : ‖a‖ = 1 := by simpa using ha
    have hHa : ‖H a‖ ≤ 1 := by
      have := hmaps (Metric.sphere_subset_closedBall ha); simpa [hB] using this
    have hne : ‖a + H a‖ ≠ 0 := by rw [halign a ha]; norm_num
    obtain ⟨g, hg1, hga⟩ := exists_dual_vector ℝ (a + H a) hne
    have h1 : g a ≤ 1 := by
      have := g.le_opNorm a
      rw [hg1, ha1, Real.norm_eq_abs] at this
      linarith [le_abs_self (g a)]
    have h2 : g (H a) ≤ 1 := by
      have := g.le_opNorm (H a)
      rw [hg1, Real.norm_eq_abs] at this
      linarith [le_abs_self (g (H a))]
    have hsum : g a + g (H a) = 2 := by rw [← map_add, hga, halign a ha]; norm_num
    have hval : g ((1 - α) • a + α • H a) = 1 := by
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      have : g a = 1 := by linarith
      have : g (H a) = 1 := by linarith
      simp [*]
    have := g.le_opNorm ((1 - α) • a + α • H a)
    rw [hg1, one_mul, hval] at this
    simpa using this
  -- P maps the ball onto itself.
  have honto : ∀ y ∈ B, ∃ x ∈ B, P x = y := by
    intro y hy
    have hy' : ‖y‖ ≤ 1 - 0 := by simpa [hB] using hy
    obtain ⟨x, hx, hPx⟩ := Plasticity.A01.averaged_covers H hmaps hlip α 0 (by norm_num) (by norm_num)
      le_rfl (by norm_num) hPa y hy'
    exact ⟨x, hx, hPx⟩
  have hPmaps : Set.MapsTo P B B := by
    intro x hx
    have hHx : H x ∈ B := hmaps hx
    exact (convex_closedBall (0 : X) 1) hx hHx (by norm_num) (by norm_num) (by norm_num)
  have honto_iter : ∀ n : ℕ, ∀ y ∈ B, ∃ x ∈ B, P^[n] x = y := by
    intro n
    induction n with
    | zero => exact fun y hy => ⟨y, hy, rfl⟩
    | succ n ih =>
      intro y hy
      obtain ⟨z, hz, hPz⟩ := honto y hy
      obtain ⟨x, hx, hx'⟩ := ih z hz
      exact ⟨x, hx, by rw [Function.iterate_succ_apply', hx', hPz]⟩
  -- Uniform asymptotic regularity and surjectivity of the iterates force P = I on the ball.
  have hfix : ∀ y ∈ B, P y = y := by
    intro y hy
    by_contra hne
    have hpos : 0 < ‖P y - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    obtain ⟨N, hN⟩ := Plasticity.Ext.UniformAsymptoticRegularity B (convex_closedBall 0 1)
      Metric.isBounded_closedBall H hmaps hlip α (by norm_num) (by norm_num) (‖P y - y‖ / 2) (by linarith)
    obtain ⟨x, hx, hxy⟩ := honto_iter N y hy
    have := hN N le_rfl x hx
    rw [Function.iterate_succ_apply', hxy] at this
    have hPy : P y = (1 - α) • y + α • H y := rfl
    rw [← hPy] at this
    linarith
  intro y hy
  have h := hfix y hy
  simp only [hP] at h
  have : α • (H y - y) = 0 := by
    have : (1 - α) • y + α • H y - y = α • (H y - y) := by module
    rw [← this, h, sub_self]
  have hα0 : α ≠ 0 := by norm_num [hα]
  simpa [sub_eq_zero] using (smul_eq_zero.mp this).resolve_left hα0
