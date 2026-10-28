-- Prove2me | solution 1 for RatingsAdvert.AdInterval.root_unique
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:16:36.832047+00:00
-- url     : https://prove2.me/submissions/252343c5-a664-44f3-b5e1-926cff690311

import Mathlib
import Definitions.Def_RatingsAdvert_AdInterval_Model

open RatingsAdvert.AdInterval

namespace Aux_RatingsAdvert_RU

theorem root_aux (g : ℝ → ℝ) (hc : ContinuousOn g (Set.Icc 0 1)) (ha : StrictAntiOn g (Set.Icc 0 1))
    (h0 : 0 < g 0) (h1 : g 1 < 0) :
    (∃! z : ℝ, z ∈ Set.Icc (0 : ℝ) 1 ∧ g z = 0) ∧
      ∀ z ∈ Set.Icc (0 : ℝ) 1, g z = 0 → z ∈ Set.Ioo (0 : ℝ) 1 := by
  have hex : (0 : ℝ) ∈ g '' Set.Icc 0 1 :=
    intermediate_value_Icc' zero_le_one hc ⟨h1.le, h0.le⟩
  obtain ⟨z, hz, hgz⟩ := hex
  refine ⟨⟨z, ⟨hz, hgz⟩, fun w ⟨hw, hgw⟩ => ha.injOn hw hz (hgw.trans hgz.symm)⟩, ?_⟩
  intro w hw hgw
  refine ⟨lt_of_le_of_ne hw.1 ?_, lt_of_le_of_ne hw.2 ?_⟩
  · intro h; rw [← h] at hgw; linarith
  · intro h; rw [h] at hgw; linarith

end Aux_RatingsAdvert_RU

theorem solution (P : Params) (hS : P.Standing) (hI : P.Interior) :
    (∃! z : ℝ, z ∈ Set.Icc (0 : ℝ) 1 ∧ ((1 + P.beta - z * P.tau) / 2) ^ 2 = deriv P.A z) ∧
      (∀ z ∈ Set.Icc (0 : ℝ) 1, ((1 + P.beta - z * P.tau) / 2) ^ 2 = deriv P.A z →
        z ∈ Set.Ioo (0 : ℝ) 1) ∧
      (∃! z : ℝ, z ∈ Set.Icc (0 : ℝ) 1 ∧
        ((1 + P.beta - z * P.tau) / 2) ^ 2 - P.tau * (1 + P.beta - P.tau) / 2 = deriv P.A z) ∧
      ∀ z ∈ Set.Icc (0 : ℝ) 1,
        ((1 + P.beta - z * P.tau) / 2) ^ 2 - P.tau * (1 + P.beta - P.tau) / 2 = deriv P.A z →
        z ∈ Set.Ioo (0 : ℝ) 1 := by
  obtain ⟨hτ0, hτ5, hβ0, hβ5, hA2, _, hA1, hA2', _⟩ := hS
  have hcont : Continuous (deriv P.A) := hA2.continuous_deriv (by norm_num)
  have hdiff : Differentiable ℝ (deriv P.A) := by
    have h : ContDiff ℝ (1 + 1) P.A := by rw [one_add_one_eq_two]; exact hA2
    exact ((contDiff_succ_iff_deriv.mp h).2.2).differentiable (by norm_num)
  have hmono : StrictMonoOn (deriv P.A) (Set.Icc 0 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 1) hcont.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    have := hA2' x ⟨hx.1.le, hx.2.le⟩
    have : 0 < P.tau / P.beta := div_pos hτ0 hβ0
    linarith
  have hL : ∀ c : ℝ, StrictAntiOn (fun z => ((1 + P.beta - z * P.tau) / 2) ^ 2 - c - deriv P.A z)
      (Set.Icc 0 1) := by
    intro c a ha b hb hab
    have h1 := hmono ha hb hab
    have hpos : 0 < 1 + P.beta - b * P.tau := by nlinarith [hb.2]
    have hlt : 1 + P.beta - b * P.tau < 1 + P.beta - a * P.tau := by nlinarith
    simp only
    nlinarith
  have hC : ∀ c : ℝ, ContinuousOn (fun z => ((1 + P.beta - z * P.tau) / 2) ^ 2 - c - deriv P.A z)
      (Set.Icc 0 1) := by
    intro c
    exact (((continuous_const.sub (continuous_id.mul continuous_const)).div_const 2).pow 2
      |>.sub continuous_const |>.sub hcont).continuousOn
  have hc0 : 0 < P.tau * (1 + P.beta - P.tau) / 2 := by
    have : 0 < 1 + P.beta - P.tau := by linarith
    positivity
  have R1 := Aux_RatingsAdvert_RU.root_aux _ (hC 0) (hL 0)
    (by show (0:ℝ) < _; have := hI.1; nlinarith) (by show _ < (0:ℝ); have := hI.2; nlinarith)
  have R2 := Aux_RatingsAdvert_RU.root_aux _ (hC (P.tau * (1 + P.beta - P.tau) / 2))
    (hL _) (by show (0:ℝ) < _; have := hI.1; nlinarith) (by show _ < (0:ℝ); have := hI.2; nlinarith)
  simp only [sub_zero, sub_eq_zero] at R1 R2
  exact ⟨R1.1, R1.2, R2.1, R2.2⟩
