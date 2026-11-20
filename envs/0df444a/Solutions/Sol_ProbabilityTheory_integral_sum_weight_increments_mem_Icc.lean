-- Prove2me | solution 1 for ProbabilityTheory.integral_sum_weight_increments_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T08:10:02.212516+00:00
-- url     : https://prove2.me/submissions/6eea5d53-6fda-45d4-8bc0-4e6d5efa7cf6

import Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_MaximalInequality_F001

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

end Bridge

/-! ### Upcrossing and alternation bounds along finite time sets -/

section UpcrossingBound

variable {a b : ℝ} {t : ι} {F : Finset ι} {m : ℕ}

end UpcrossingBound

/-! ### Selection of alternating tuples from frequent oscillation -/

section Selection

variable [TopologicalSpace ι] [OrderTopology ι]

variable {T : Set ι} {x d : ι} {a b : ℝ} {ω : Ω}

end Selection

/-! ### Maximal inequality along finite time sets -/

section Maximal

variable {t : ι} {F : Finset ι} {lam : ℝ}

-- todo name
theorem AuxE.eps [OrderBot ι] {t : ι} (n : ℕ) {idx : ℕ → ι}
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


theorem _root_.solution [OrderBot ι]
    (hXint : ∀ s, Integrable (X s) μ) {C : ℝ}
    (hC : ∀ S : ElementaryPredictableSet 𝓕, μ[(S.indicator (1 : ℝ) ● X) t] ≤ C)
    {n : ℕ} {idx : ℕ → ι} (hidx : Monotone idx) (hidxt : ∀ k, idx k ≤ t)
    {W : ℕ → Ω → ℝ} (hW01 : ∀ k, k < n → ∀ ω, W k ω = 0 ∨ W k ω = 1)
    (hWmeas : ∀ k, k < n → Measurable[𝓕 (idx k)] (W k)) :
    ∫ ω, (∑ k ∈ range n, W k ω * (X (idx (k + 1)) ω - X (idx k) ω)) ∂μ
        ∈ Set.Icc (-(C + ∫ ω, |X (idx n) ω - X (idx 0) ω| ∂μ)) C := by
  have key : ∀ V : ℕ → Ω → ℝ, (∀ k, k < n → ∀ ω, V k ω = 0 ∨ V k ω = 1) →
      (∀ k, k < n → Measurable[𝓕 (idx k)] (V k)) →
      ∫ ω, (∑ k ∈ range n, V k ω * (X (idx (k + 1)) ω - X (idx k) ω)) ∂μ ≤ C := by
    intro V hV01 hVmeas
    have h := hC (elemPredSetOfSeq hidx n hVmeas)
    have heq : (fun ω => ((elemPredSetOfSeq hidx n hVmeas).indicator (1 : ℝ) ● X) t ω)
        = fun ω => ∑ k ∈ range n, V k ω * (X (idx (k + 1)) ω - X (idx k) ω) :=
      funext fun ω => AuxE.eps n hidx hidxt hV01 hVmeas ω
    rw [heq] at h
    exact h
  have hint : ∀ V : ℕ → Ω → ℝ, (∀ k, k < n → ∀ ω, V k ω = 0 ∨ V k ω = 1) →
      (∀ k, k < n → Measurable[𝓕 (idx k)] (V k)) →
      Integrable (fun ω => ∑ k ∈ range n, V k ω * (X (idx (k + 1)) ω - X (idx k) ω)) μ := by
    intro V hV01 hVmeas
    refine integrable_sum_weight_increments hXint
      (fun k hk => ((hVmeas k hk).mono (𝓕.le _) le_rfl).aestronglyMeasurable) ?_
    intro k hk ω
    rcases hV01 k hk ω with h | h <;> simp [h]
  refine ⟨?_, key W hW01 hWmeas⟩
  set W' : ℕ → Ω → ℝ := fun k ω => 1 - W k ω with hW'
  have hW'01 : ∀ k, k < n → ∀ ω, W' k ω = 0 ∨ W' k ω = 1 := by
    intro k hk ω
    rcases hW01 k hk ω with h | h <;> simp [W', h]
  have hW'meas : ∀ k, k < n → Measurable[𝓕 (idx k)] (W' k) := fun k hk =>
    measurable_const.sub (hWmeas k hk)
  have h1 := key W' hW'01 hW'meas
  have hsum : ∀ ω, ∑ k ∈ range n, W' k ω * (X (idx (k + 1)) ω - X (idx k) ω)
      = (X (idx n) ω - X (idx 0) ω)
        - ∑ k ∈ range n, W k ω * (X (idx (k + 1)) ω - X (idx k) ω) := by
    intro ω
    simp only [W', sub_mul, one_mul, Finset.sum_sub_distrib]
    have := Finset.sum_range_sub (fun k => X (idx k) ω) n
    simp only [Finset.sum_sub_distrib] at this
    linarith
  simp_rw [hsum] at h1
  rw [integral_sub (f := fun ω => X (idx n) ω - X (idx 0) ω) ((hXint _).sub (hXint _)) (hint W hW01 hWmeas)] at h1
  have h2' : -∫ ω, |X (idx n) ω - X (idx 0) ω| ∂μ ≤ ∫ ω, (X (idx n) ω - X (idx 0) ω) ∂μ := by
    rw [← integral_neg]
    exact integral_mono ((hXint _).sub (hXint _)).abs.neg ((hXint _).sub (hXint _))
      fun ω => neg_abs_le (X (idx n) ω - X (idx 0) ω)
  linarith

end Maximal

end ProbabilityTheory
