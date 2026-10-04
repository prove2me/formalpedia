-- Prove2me | solution 1 for ProcessingNetworks.ProportionalFairness.entropy_lyapunov_nonneg
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:19:17.55019+00:00
-- url     : https://prove2.me/submissions/858c39da-5042-4f2a-bf9b-ad4c1093671b

import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_FluidModel
import Definitions.Def_ProcessingNetworks_ProportionalFairness_EntropyLyapunov

namespace ProcessingNetworks.ProportionalFairness.EntropyNonnegCE

open ProcessingNetworks.ProportionalFairness

def S : Set (Fin 1 → ℝ) := {x | 0 ≤ x 0 ∧ x 0 ≤ 1}

theorem dom : IsPFDomain S := by
  refine ⟨?_, ?_, ?_, ?_, ⟨fun _ => 1, ⟨zero_le_one, le_refl _⟩, fun _ => one_pos⟩⟩
  · refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨1, fun x hx => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    fin_cases i
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by have := hx.1; simp only [Fin.zero_eta] at this ⊢; linarith,
      by have := hx.2; simp only [Fin.zero_eta] at this ⊢; linarith⟩
  · exact (isClosed_le continuous_const (continuous_apply 0)).inter
      (isClosed_le (continuous_apply 0) continuous_const)
  · intro x hx y hy a b ha hb hab
    simp only [S, Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hy ⊢
    constructor <;> nlinarith [hx.1, hx.2, hy.1, hy.2]
  · intro x hx y hy hyx
    exact ⟨hy 0, le_trans (hyx 0) hx.2⟩

theorem f_eq (c : ℝ) (x : Fin 1 → ℝ) : f (fun _ => c) x = (c : EReal) * extLog (x 0) := by
  simp [f]

theorem maxim (c : ℝ) (hc : 0 < c) : IsPFMaximizer S (fun _ => c) (fun _ => 1) := by
  refine ⟨⟨zero_le_one, le_refl _⟩, fun y hy => ?_⟩
  rw [f_eq, f_eq]
  have h1 : extLog ((fun _ : Fin 1 => (1 : ℝ)) 0) = 0 := by simp [extLog]
  rw [h1, mul_zero]
  unfold extLog
  split_ifs with h
  · rw [EReal.coe_mul_bot_of_pos hc]; exact bot_le
  · rw [← EReal.coe_mul, ← EReal.coe_zero, EReal.coe_le_coe_iff]
    exact mul_nonpos_of_nonneg_of_nonpos hc.le
      (Real.log_nonpos hy.1 hy.2)

theorem maxim_unique (c : ℝ) (hc : 0 < c) (x : Fin 1 → ℝ) (hx : IsPFMaximizer S (fun _ => c) x) :
    x 0 = 1 := by
  have hge := hx.2 _ (maxim c hc).1
  rw [f_eq, f_eq] at hge
  have h1 : extLog ((fun _ : Fin 1 => (1 : ℝ)) 0) = 0 := by simp [extLog]
  rw [h1, mul_zero] at hge
  have hS := hx.1
  unfold extLog at hge
  split_ifs at hge with h
  · rw [EReal.coe_mul_bot_of_pos hc] at hge; exact absurd hge (by simp)
  · rw [← EReal.coe_mul, ← EReal.coe_zero, EReal.coe_le_coe_iff] at hge
    have hpos : 0 < x 0 := lt_of_le_of_ne hS.1 (Ne.symm h)
    have hlog : 0 ≤ Real.log (x 0) := by
      by_contra hneg; push_neg at hneg; nlinarith
    have hle : Real.log (x 0) ≤ 0 := Real.log_nonpos hS.1 hS.2
    have h0 : Real.log (x 0) = 0 := le_antisymm hle hlog
    rcases Real.log_eq_zero.mp h0 with h' | h' | h'
    · exact absurd h' h
    · exact h'
    · linarith

theorem psi_eq (c : ℝ) (hc : 0 < c) : psi S (fun _ => c) 0 = 1 := by
  have hex : ∃ x, IsPFMaximizer S (fun _ => c) x := ⟨_, maxim c hc⟩
  simp only [psi, if_pos hc, dif_pos hex]
  exact maxim_unique c hc _ (Classical.choose_spec hex)

theorem agg (x : Fin 1 → ℝ) : groupAggregate id x = x := by
  funext l; fin_cases l
  unfold groupAggregate
  rw [Finset.sum_eq_single 0]
  · rfl
  · intro b _ hb; exact absurd (Subsingleton.elim b 0) hb
  · intro h; simp at h

noncomputable def dat : PFUnitaryNetworkData 1 1 :=
  { lam := fun _ => 2, m := fun _ => 1, hm := fun _ => one_pos, P := 0, grp := id,
    TildeAllocSet := S }

theorem hsol : IsPFFluidModelSolution dat (fun t _ => 2 * t) (fun t _ => t) (fun t _ => t)
    (fun t _ => 1 + t) := by
  refine ⟨fun t _ => ?_, fun t ht _ => by linarith, fun t _ i => ?_, fun t _ i => ?_,
    ⟨rfl, fun a b hab i => hab, 1, fun s t _ hst i => ?_⟩, fun t ht i _ => ?_⟩
  · funext i; ring
  · simp [dat]
  · simp [dat]
  · rw [abs_of_nonneg (by linarith)]; linarith
  · have hc : (0 : ℝ) < 1 + t := by linarith
    show HasDerivAt (fun u => u) _ t
    have : groupAggregate dat.grp ((fun t _ => 1 + t) t) = fun _ => 1 + t := agg _
    rw [this]
    fin_cases i
    show HasDerivAt (fun u => u) (psi S (fun _ => 1 + t) 0 * (1 + t) / (1 + t)) t
    rw [psi_eq _ hc, one_mul, div_self hc.ne']
    exact hasDerivAt_id t

end ProcessingNetworks.ProportionalFairness.EntropyNonnegCE

open ProcessingNetworks.ProportionalFairness in
theorem solution : ¬ (∀ {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (hdom : IsPFDomain dat.TildeAllocSet) (hlam : ∀ i, 0 ≤ dat.lam i)
    (hP_nonneg : ∀ i j, 0 ≤ dat.P i j) (hP_rowsum : ∀ i, ∑ j, dat.P i j ≤ 1)
    (hP_transient : ∀ i j, Filter.Tendsto (fun n => (dat.P ^ n) i j) Filter.atTop (nhds 0)) (alpha : Fin I → ℝ)
    (Ah Dh Th Zh : ℝ → Fin I → ℝ) (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh)
    (halpha : IsTotalArrivalRates dat alpha) (hα : ∀ i, 0 < alpha i) (t : ℝ) (ht : 0 ≤ t),
    0 ≤ phi Dh Zh alpha t ∧ (Zh t ≠ 0 → 0 < phi Dh Zh alpha t)) := by
  intro h
  have := (h EntropyNonnegCE.dat EntropyNonnegCE.dom (fun _ => by simp [EntropyNonnegCE.dat])
    (fun _ _ => by simp [EntropyNonnegCE.dat]) (fun _ => by simp [EntropyNonnegCE.dat])
    (fun i j => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      simp [EntropyNonnegCE.dat, zero_pow (show n ≠ 0 by omega)])
    (fun _ => 2) _ _ _ _ EntropyNonnegCE.hsol
    (by funext i; simp [EntropyNonnegCE.dat]) (fun _ => two_pos) 0 le_rfl).1
  unfold phi at this
  have hd : derivWithin (fun s : ℝ => s) (Set.Ici 0) 0 = 1 :=
    derivWithin_id _ _ (uniqueDiffWithinAt_Ici 0)
  simp only [Fin.sum_univ_one, hd] at this
  rw [if_neg (by norm_num), add_zero, one_mul] at this
  have : Real.log (1 / 2) < 0 := Real.log_neg (by norm_num) (by norm_num)
  linarith


