-- Prove2me | solution 1 for PrivLearn.LocalSim.randomizer_is_local
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T18:11:29.258736+00:00
-- url     : https://prove2.me/submissions/8fa4b2c3-c1e5-47d9-b787-fac1ce893ae5

import Mathlib
import Definitions.Def_PrivLearn_LocalSim_Privacy
import Definitions.Def_PrivLearn_LocalSim_Simulation

open MeasureTheory

open PrivLearn.LocalSim in
theorem solution {Dom : Type*} (g : Dom → ℝ) (b ε : ℝ) (hb : 0 < b) (hε : 0 < ε)
    (hg : ∀ u, |g u| ≤ b) :
    IsLocalRandomizer (randomizerLaw g (2 * b / ε)) ε := by
  classical
  intro u u' S hS
  set s := 2 * b / ε with hs
  have hspos : 0 < s := by positivity
  set p : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp (-|x| / s) / (2 * s)) with hp
  have hpm : Measurable p := by
    apply ENNReal.measurable_ofReal.comp
    exact ((Real.measurable_exp.comp ((measurable_id.abs.neg).div_const s)).div_const _)
  have key : ∀ c : ℝ, ((PrivLearn.Generic.laplace s).map fun η => c + η) S =
      ∫⁻ x, (if c + x ∈ S then p x else 0) := by
    intro c
    have hT : MeasurableSet ((fun η => c + η) ⁻¹' S) := measurable_const_add c hS
    rw [Measure.map_apply (measurable_const_add c) hS]
    unfold PrivLearn.Generic.laplace
    rw [withDensity_apply _ hT, ← lintegral_indicator hT]
    simp only [Set.indicator_apply, Set.mem_preimage, hp]
  unfold randomizerLaw
  rw [key, key]
  set c := g u
  set c' := g u'
  set d := c' - c with hd
  have hdb : |d| ≤ ε * s := by
    have h1 := hg u; have h2 := hg u'
    have : ε * s = 2 * b := by rw [hs]; field_simp
    rw [this, hd]
    calc |c' - c| ≤ |c'| + |c| := abs_sub _ _
      _ ≤ 2 * b := by linarith
  have hshift : ∫⁻ x, (if c + x ∈ S then p x else 0) =
      ∫⁻ x, (if c' + x ∈ S then p (x + d) else 0) := by
    rw [← lintegral_add_right_eq_self _ d]
    congr 1
    funext x
    rw [show c + (x + d) = c' + x by rw [hd]; ring]
  rw [hshift, ← lintegral_const_mul _ (by
    exact Measurable.ite (measurable_const_add c' hS) hpm measurable_const)]
  apply lintegral_mono
  intro x
  dsimp only
  split_ifs
  · simp only [hp]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    have hpt : Real.exp (-|x + d| / s) ≤ Real.exp ε * Real.exp (-|x| / s) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h1 : |x| ≤ |x + d| + |d| := by
        calc |x| = |(x + d) - d| := by ring_nf
          _ ≤ |x + d| + |d| := abs_sub _ _
      have h2 : |d| / s ≤ ε := by rw [div_le_iff₀ hspos]; linarith
      have h3 : |x| / s ≤ |x + d| / s + |d| / s := by
        rw [← add_div]; exact div_le_div_of_nonneg_right h1 hspos.le
      rw [neg_div, neg_div]
      linarith
    have hden : 0 < 2 * s := by positivity
    calc Real.exp (-|x + d| / s) / (2 * s) ≤ Real.exp ε * Real.exp (-|x| / s) / (2 * s) :=
          div_le_div_of_nonneg_right hpt hden.le
      _ = Real.exp ε * (Real.exp (-|x| / s) / (2 * s)) := by ring
  · simp
