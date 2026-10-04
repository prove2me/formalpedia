-- Prove2me | solution 1 for ProcessingNetworks.ProportionalFairness.pf_aggregation_property
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:16:10.283812+00:00
-- url     : https://prove2.me/submissions/6e435c39-a6ab-4c4b-9cce-b1e7ab1d5c12

import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_PFOptimization
import Definitions.Def_ProcessingNetworks_ProportionalFairness_Aggregation

namespace ProcessingNetworks.ProportionalFairness.PFAggCE

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

def SA : Set (Fin 1 → ℝ) := {x | (∀ i, 0 ≤ x i) ∧ groupAggregate id x ∈ S}

theorem agg (x : Fin 1 → ℝ) : groupAggregate id x 0 = x 0 := by
  unfold groupAggregate
  rw [Finset.sum_eq_single 0]
  · intro b _ hb; exact absurd (Subsingleton.elim b 0) hb
  · intro h; simp at h

theorem agg_fun (x : Fin 1 → ℝ) : groupAggregate id x = x := by
  funext l; fin_cases l; exact agg x

theorem lhs_nonneg : 0 ≤ psi SA (fun _ => 1) 0 := by
  unfold psi
  split_ifs with h1 h2
  · exact (Classical.choose_spec h2).1.1 0
  · exact le_refl _
  · exact le_refl _

end ProcessingNetworks.ProportionalFairness.PFAggCE

open ProcessingNetworks.ProportionalFairness in
theorem solution : ¬ (∀ {I L : ℕ} (AllocSet : Set (Fin I → ℝ)) (TildeAllocSet : Set (Fin L → ℝ))
    (grp : Fin I → Fin L) (hdom : IsPFDomain TildeAllocSet)
    (hAllocSet : ∀ x : Fin I → ℝ,
      x ∈ AllocSet ↔ (∀ i, 0 ≤ x i) ∧ groupAggregate grp x ∈ TildeAllocSet)
    (z : Fin I → ℝ) (hz : ∀ i, 0 ≤ z i) (i : Fin I),
    psi AllocSet z i =
      psi TildeAllocSet (groupAggregate grp z) (grp i) * z i / groupAggregate grp z (grp i)) := by
  intro h
  have := h PFAggCE.SA PFAggCE.S id PFAggCE.dom (fun x => Iff.rfl) (fun _ => 1)
    (fun _ => zero_le_one) 0
  rw [PFAggCE.agg_fun] at this
  simp only [id, mul_one, div_one] at this
  have h1 := PFAggCE.lhs_nonneg
  have h2 := PFAggCE.psi_neg
  linarith


