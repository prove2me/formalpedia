-- Prove2me | solution 1 for ProbabilityTheory.integral_elemPredSetOfSeq
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T08:08:31.515533+00:00
-- url     : https://prove2.me/submissions/813ab851-8aaf-48a4-8f7e-d08b13ab919f

import Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_MaximalInequality_F000

/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohit Manokaran, Rémy Degenne
-/

/-! # Maximal inequality for real quasimartingales -/

@[expose] public section

open MeasureTheory Finset Filter
open scoped ENNReal Topology MeasureTheory ProbabilityTheory.SimpleProcess

namespace ProbabilityTheory

variable {ι Ω : Type*} [LinearOrder ι]
  {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ} {μ : Measure Ω}
  {X : ι → Ω → ℝ} {τ σ : Ω → WithTop ι} {i : ι}

section Bridge

variable {F : Finset ι} {t : ι} {k l : ℕ}

theorem _root_.solution [OrderBot ι] {t : ι} (n : ℕ) {idx : ℕ → ι}
    (hidx : Monotone idx) (hidxt : ∀ k, idx k ≤ t) {W : ℕ → Ω → ℝ}
    (hW01 : ∀ k, k < n → ∀ ω, W k ω = 0 ∨ W k ω = 1)
    (hWmeas : ∀ k, k < n → Measurable[𝓕 (idx k)] (W k)) (ω : Ω) :
    ((elemPredSetOfSeq hidx n hWmeas).indicator (1 : ℝ) ● X) t ω =
      ∑ k ∈ range n, W k ω * (X (idx (k + 1)) ω - X (idx k) ω) := by
  classical
  have hst : ∀ s, s ≤ t → stoppedProcess X (fun _ ↦ (t : WithTop ι)) s ω = X s ω := fun s hs =>
    stoppedProcess_eq_of_le (WithTop.coe_le_coe.2 hs)
  set K : Finset ℕ := {k ∈ range n | idx k < idx (k + 1)} with hK
  have hinj : ∀ x ∈ K, ∀ y ∈ K, (idx x, idx (x + 1)) = (idx y, idx (y + 1)) → x = y := by
    intro x hx y hy hxy
    have hx' := (Finset.mem_filter.1 hx).2
    have hy' := (Finset.mem_filter.1 hy).2
    have h1 : idx x = idx y := (Prod.ext_iff.1 hxy).1
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := hidx (Nat.succ_le_of_lt h)
      rw [← h1] at this
      exact absurd hx' (not_lt.2 this)
    · have := hidx (Nat.succ_le_of_lt h)
      rw [h1] at this
      exact absurd hy' (not_lt.2 this)
  rw [ElementaryPredictableSet.integral_indicator_apply]
  simp only [elemPredSetOfSeq]
  rw [Finset.sum_image hinj]
  have hne : ∀ k ∈ range n, W k ω * (X (idx (k + 1)) ω - X (idx k) ω) ≠ 0 →
      idx k < idx (k + 1) := by
    intro k _ hne
    by_contra hlt
    have heq : idx k = idx (k + 1) := le_antisymm (hidx (Nat.le_succ k)) (not_lt.1 hlt)
    apply hne
    rw [heq, sub_self, mul_zero]
  rw [← Finset.sum_filter_of_ne hne]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hex : ∃ k' ∈ K, (idx k', idx (k' + 1)) = (idx k, idx (k + 1)) := ⟨k, hk, rfl⟩
  rw [dif_pos hex]
  have hch : hex.choose = k := hinj _ hex.choose_spec.1 _ hk hex.choose_spec.2
  rw [hch]
  have hkn : k < n := Finset.mem_range.1 (Finset.mem_filter.1 hk).1
  rcases hW01 k hkn ω with h | h
  · simp [Set.indicator, h]
  · simp [Set.indicator, h, hst _ (hidxt _)]

end Bridge

end ProbabilityTheory
