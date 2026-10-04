-- Prove2me | solution 1 for ProcessingNetworks.ProportionalFairness.pf_allocation_properties
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:14:57.340533+00:00
-- url     : https://prove2.me/submissions/d59a01e9-3dc8-4b29-a4f4-dac3e6dd5270

import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_PFOptimization

namespace ProcessingNetworks.ProportionalFairness.PFAllocCE

open ProcessingNetworks.ProportionalFairness

def S : Set (Fin 1 → ℝ) := {x | -2 ≤ x 0 ∧ x 0 ≤ 1}

theorem dom : IsPFDomain S := by
  refine ⟨?_, ?_, ?_, ?_, ⟨fun _ => 1, ⟨by norm_num, le_refl _⟩, fun _ => one_pos⟩⟩
  · refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨2, fun x hx => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by norm_num)]
    intro i
    fin_cases i
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨hx.1, by have := hx.2; simp only [Fin.zero_eta] at this ⊢; linarith⟩
  · exact (isClosed_le continuous_const (continuous_apply 0)).inter
      (isClosed_le (continuous_apply 0) continuous_const)
  · intro x hx y hy a b ha hb hab
    simp only [S, Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hy ⊢
    constructor <;> nlinarith [hx.1, hx.2, hy.1, hy.2]
  · intro x hx y hy hyx
    exact ⟨by linarith [hy 0], le_trans (hyx 0) hx.2⟩

theorem f_eq (x : Fin 1 → ℝ) : f (fun _ => 1) x = extLog (x 0) := by
  simp [f]

theorem extLog_le (x : Fin 1 → ℝ) (hx : x ∈ S) : extLog (x 0) ≤ (Real.log 2 : EReal) := by
  unfold extLog
  split_ifs with h
  · exact bot_le
  · rw [EReal.coe_le_coe_iff, ← Real.log_abs]
    exact Real.log_le_log (abs_pos.mpr h) (abs_le.mpr ⟨hx.1, by linarith [hx.2]⟩)

theorem maxim : IsPFMaximizer S (fun _ => 1) (fun _ => -2) := by
  refine ⟨⟨le_refl _, by norm_num⟩, fun y hy => ?_⟩
  rw [f_eq, f_eq]
  have : extLog ((fun _ : Fin 1 => (-2 : ℝ)) 0) = (Real.log 2 : EReal) := by
    simp [extLog, Real.log_neg_eq_log]
  rw [this]
  exact extLog_le y hy

theorem psi_neg : psi S (fun _ => 1) 0 < 0 := by
  have hex : ∃ x, IsPFMaximizer S (fun _ => 1) x := ⟨_, maxim⟩
  have hspec := Classical.choose_spec hex
  simp only [psi, if_pos one_pos, dif_pos hex]
  set x := Classical.choose hex
  have hge := hspec.2 _ maxim.1
  rw [f_eq, f_eq] at hge
  have h2 : extLog ((fun _ : Fin 1 => (-2 : ℝ)) 0) = (Real.log 2 : EReal) := by
    simp [extLog, Real.log_neg_eq_log]
  rw [h2] at hge
  by_contra hcon
  push_neg at hcon
  have hx1 := hspec.1.2
  unfold extLog at hge
  split_ifs at hge with h0
  · exact absurd hge (by simp)
  · rw [EReal.coe_le_coe_iff] at hge
    have hpos : 0 < x 0 := lt_of_le_of_ne hcon (Ne.symm h0)
    have : Real.log (x 0) ≤ 0 := Real.log_nonpos hpos.le hx1
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith

end ProcessingNetworks.ProportionalFairness.PFAllocCE

open ProcessingNetworks.ProportionalFairness in
theorem solution : ¬ (∀ {I : ℕ} (AllocSet : Set (Fin I → ℝ)) (hdom : IsPFDomain AllocSet)
    (z : Fin I → ℝ) (hz : ∀ i, 0 ≤ z i),
    IsPFMaximizer AllocSet z (psi AllocSet z) ∧
    (∀ i, 0 < z i →
      0 < psi AllocSet z i ∧ ∀ x, IsPFMaximizer AllocSet z x → x i = psi AllocSet z i) ∧
    ((∃ i, 0 < z i) → ∀ x ∈ AllocSet, ∃ i, 0 < z i ∧ x i ≤ psi AllocSet z i) ∧
    (∀ r : ℝ, 0 < r → ∀ i, 0 < z i → psi AllocSet (fun i => r * z i) i = psi AllocSet z i) ∧
    (∀ i, 0 < z i →
      ContinuousWithinAt (fun w => psi AllocSet w i) {w : Fin I → ℝ | ∀ i, 0 ≤ w i} z) ∧
    (z ≠ 0 → ∀ x ∈ interior AllocSet, f z x < f z (psi AllocSet z)) ∧
    ContinuousWithinAt (fun w => f w (psi AllocSet w)) {w : Fin I → ℝ | ∀ i, 0 ≤ w i} z) := by
  intro h
  have := (h PFAllocCE.S PFAllocCE.dom (fun _ => 1) (fun _ => zero_le_one)).2.1 0 one_pos
  linarith [this.1, PFAllocCE.psi_neg]


