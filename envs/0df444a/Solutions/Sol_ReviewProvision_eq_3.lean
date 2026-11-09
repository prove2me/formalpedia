-- Prove2me | solution 1 for ReviewProvision.eq_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T08:28:59.841858+00:00
-- url     : https://prove2.me/submissions/4b6da413-524d-421c-8c4b-b12ecb31d801

import Mathlib
import Definitions.Def_ReviewProvision_secondPeriodPayoff

namespace Aux_ReviewProvision_eq3
open ReviewProvision

theorem key (p : Params) (w : ℝ) :
    IsGreatest (clusterRevenue p w '' Set.Ici 0) (clusterRevenue p w (max (w / (2 * p.h)) 0)) ∧
    (∀ r, 0 ≤ r → clusterRevenue p w r = clusterRevenue p w (max (w / (2 * p.h)) 0) →
        r = max (w / (2 * p.h)) 0) ∧
    clusterRevenue p w (max (w / (2 * p.h)) 0) = p.m * (max w 0) ^ 2 / (4 * p.h) := by
  have hh := p.h_pos
  have hm := p.m_pos
  rcases le_or_gt 0 w with hw | hw
  · have e1 : max (w / (2 * p.h)) 0 = w / (2 * p.h) := max_eq_left (by positivity)
    have e2 : max w 0 = w := max_eq_left hw
    rw [e1, e2]
    have hid : ∀ r, clusterRevenue p w (w / (2 * p.h)) - clusterRevenue p w r =
        p.m * p.h * (r - w / (2 * p.h)) ^ 2 := by
      intro r; unfold clusterRevenue; field_simp; ring
    refine ⟨⟨⟨_, Set.mem_Ici.mpr (by positivity), rfl⟩, ?_⟩, ?_, ?_⟩
    · rintro _ ⟨r, _, rfl⟩
      have := hid r
      have : 0 ≤ p.m * p.h * (r - w / (2 * p.h)) ^ 2 := by positivity
      linarith
    · intro r _ hr
      have h1 := hid r
      have h2 : p.m * p.h * (r - w / (2 * p.h)) ^ 2 = 0 := by linarith
      have h3 : (r - w / (2 * p.h)) ^ 2 = 0 := by
        rcases mul_eq_zero.mp h2 with h | h
        · exfalso; have : 0 < p.m * p.h := mul_pos hm hh; linarith
        · exact h
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3
      linarith
    · unfold clusterRevenue; field_simp; ring
  · have e1 : max (w / (2 * p.h)) 0 = 0 :=
      max_eq_right (div_nonpos_of_nonpos_of_nonneg hw.le (by positivity))
    have e2 : max w 0 = 0 := max_eq_right hw.le
    rw [e1, e2]
    have h0 : clusterRevenue p w 0 = 0 := by unfold clusterRevenue; ring
    refine ⟨⟨⟨0, Set.mem_Ici.mpr le_rfl, rfl⟩, ?_⟩, ?_, ?_⟩
    · rintro _ ⟨r, hr, rfl⟩
      rw [h0]
      unfold clusterRevenue
      have hr' : 0 ≤ r := hr
      have : w - p.h * r < 0 := by nlinarith
      have : (w - p.h * r) * r ≤ 0 := mul_nonpos_of_nonpos_of_nonneg this.le hr'
      nlinarith
    · intro r hr hrr
      rw [h0] at hrr
      unfold clusterRevenue at hrr
      have hne : w - p.h * r ≠ 0 := by nlinarith
      rcases mul_eq_zero.mp hrr with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · linarith
        · exact absurd h' hne
      · exact h
    · rw [h0]; simp
end Aux_ReviewProvision_eq3

open ReviewProvision in
theorem solution (p : Params) {N : ℕ} (v : Fin N → ℝ) :
    (∀ n, IsGreatest (clusterRevenue p (v n) '' Set.Ici 0)
      (clusterRevenue p (v n) (max (v n / (2 * p.h)) 0))) ∧
    (∀ n, ∀ r, 0 ≤ r →
      clusterRevenue p (v n) r = clusterRevenue p (v n) (max (v n / (2 * p.h)) 0) →
        r = max (v n / (2 * p.h)) 0) ∧
    (∀ n, optimalRevenue p (v n) = p.m * (max (v n) 0) ^ 2 / (4 * p.h)) ∧
    secondPeriodPayoff p v = ∑ n, p.m * (max (v n) 0) ^ 2 / (4 * p.h) := by
  have hopt : ∀ n, optimalRevenue p (v n) = p.m * (max (v n) 0) ^ 2 / (4 * p.h) := by
    intro n
    obtain ⟨hg, -, hval⟩ := Aux_ReviewProvision_eq3.key p (v n)
    unfold optimalRevenue
    rw [hg.csSup_eq, hval]
  refine ⟨fun n => (Aux_ReviewProvision_eq3.key p (v n)).1,
    fun n => (Aux_ReviewProvision_eq3.key p (v n)).2.1, hopt, ?_⟩
  unfold secondPeriodPayoff
  exact Finset.sum_congr rfl (fun n _ => hopt n)
