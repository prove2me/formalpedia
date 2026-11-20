-- Prove2me | solution 1 for ProbabilityTheory.mul_measureReal_exists_lt_le
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T08:06:41.484109+00:00
-- url     : https://prove2.me/submissions/0210645a-66a9-4f18-a675-7bc08cd18294

import Definitions.Def_BrownianMotion_Auxiliary_Filtration_F000
import Definitions.Def_BrownianMotion_Auxiliary_Upcrossing_F000
import Definitions.Def_BrownianMotion_Auxiliary_Upcrossing_F001
import Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_Basic_F000

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

theorem _root_.solution [IsFiniteMeasure μ]
    {g : ι → Ω → ℝ} (hg : StronglyAdapted 𝓕 g) (hgint : ∀ s, Integrable (g s) μ)
    {n : ℕ} {idx : ℕ → ι} (hidx : Monotone idx) {K : ℝ}
    (hK : ∀ W : ℕ → Ω → ℝ, (∀ k, k < n → ∀ ω, W k ω = 0 ∨ W k ω = 1) →
      (∀ k, k < n → Measurable[𝓕 (idx k)] (W k)) →
      ∫ ω, (∑ k ∈ range n, W k ω * (g (idx (k + 1)) ω - g (idx k) ω)) ∂μ ≤ K) :
    lam * μ.real {ω | ∃ k ≤ n, lam < g (idx k) ω}
      ≤ K + ∫ ω, |g (idx 0) ω| ∂μ + ∫ ω, |g (idx n) ω| ∂μ := by
  classical
  have hgm : ∀ s, Measurable (g s) := fun s => ((hg s).measurable).mono (𝓕.le s) le_rfl
  set A := {ω | ∃ k ≤ n, lam < g (idx k) ω} with hA
  let σ : Ω → ℕ := fun ω => if h : ∃ k ≤ n, lam < g (idx k) ω then Nat.find h else n
  have hσle : ∀ ω, σ ω ≤ n := by
    intro ω
    simp only [σ]
    split_ifs with h
    · exact (Nat.find_spec h).1
    · exact le_rfl
  have hWσ : ∀ k ω, k < n → (k < σ ω ↔ ∀ j ≤ k, g (idx j) ω ≤ lam) := by
    intro k ω hk
    simp only [σ]
    split_ifs with h
    · rw [Nat.lt_find_iff]
      constructor
      · intro H j hj
        have := H j hj
        push_neg at this
        exact this (hj.trans hk.le)
      · intro H j hj hcon
        linarith [H j hj, hcon.2]
    · push_neg at h
      simp only [hk, true_iff]
      intro j hj
      exact h j (hj.trans hk.le)
  set W : ℕ → Ω → ℝ := fun k ω => if k < σ ω then 1 else 0 with hW
  have hW01 : ∀ k, k < n → ∀ ω, W k ω = 0 ∨ W k ω = 1 := by
    intro k _ ω
    simp only [W]
    split_ifs <;> simp
  have hWmeas : ∀ k, k < n → Measurable[𝓕 (idx k)] (W k) := by
    intro k hk
    have hset : MeasurableSet[𝓕 (idx k)] {ω | k < σ ω} := by
      have : {ω | k < σ ω} = ⋂ j ∈ Finset.range (k + 1), {ω | g (idx j) ω ≤ lam} := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_range, hWσ k ω hk]
        constructor
        · intro H j hj; exact H j (Nat.lt_succ_iff.1 hj)
        · intro H j hj; exact H j (Nat.lt_succ_iff.2 hj)
      rw [this]
      refine Finset.measurableSet_biInter _ fun j hj => ?_
      have hj' : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      exact 𝓕.mono (hidx hj') _ ((hg (idx j)).measurable measurableSet_Iic)
    exact Measurable.ite hset measurable_const measurable_const
  have hWm' : ∀ k, k < n → Measurable (W k) := fun k hk => (hWmeas k hk).mono (𝓕.le _) le_rfl
  have hKW := hK W hW01 hWmeas
  set gs : Ω → ℝ := fun ω => g (idx (σ ω)) ω with hgs_def
  have htel : ∀ ω, ∑ k ∈ range n, W k ω * (g (idx (k + 1)) ω - g (idx k) ω)
      = gs ω - g (idx 0) ω := by
    intro ω
    have : ∑ k ∈ range n, W k ω * (g (idx (k + 1)) ω - g (idx k) ω)
        = ∑ k ∈ range (σ ω), (g (idx (k + 1)) ω - g (idx k) ω) := by
      rw [← Finset.sum_range_add_sum_Ico _ (hσle ω)]
      have h1 : ∑ k ∈ range (σ ω), W k ω * (g (idx (k + 1)) ω - g (idx k) ω)
          = ∑ k ∈ range (σ ω), (g (idx (k + 1)) ω - g (idx k) ω) :=
        Finset.sum_congr rfl fun k hk => by simp [W, Finset.mem_range.1 hk]
      have h2 : ∑ k ∈ Ico (σ ω) n, W k ω * (g (idx (k + 1)) ω - g (idx k) ω) = 0 :=
        Finset.sum_eq_zero fun k hk => by simp [W, not_lt.2 (Finset.mem_Ico.1 hk).1]
      rw [h1, h2, add_zero]
    rw [this, Finset.sum_range_sub (fun k => g (idx k) ω)]
  have hint_sum : Integrable (fun ω => ∑ k ∈ range n,
      W k ω * (g (idx (k + 1)) ω - g (idx k) ω)) μ :=
    integrable_finset_sum _ fun k hk => ((hgint _).sub (hgint _)).bdd_mul (c := 1)
      (hWm' k (Finset.mem_range.1 hk)).aestronglyMeasurable
      (ae_of_all _ fun ω => by simp only [W]; split_ifs <;> simp)
  have hgs : Integrable gs μ := by
    have : gs = fun ω => (∑ k ∈ range n, W k ω * (g (idx (k + 1)) ω - g (idx k) ω))
        + g (idx 0) ω := funext fun ω => by rw [htel]; ring
    rw [this]; exact hint_sum.add (hgint _)
  have hAm : MeasurableSet A := by
    have : A = ⋃ k ∈ Finset.range (n + 1), {ω | lam < g (idx k) ω} := by
      ext ω
      simp only [hA, Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range, exists_prop,
        Nat.lt_succ_iff]
    rw [this]
    exact Finset.measurableSet_biUnion _ fun k _ => measurableSet_lt measurable_const (hgm _)
  have hpt : ∀ ω, lam * A.indicator 1 ω ≤ gs ω + |g (idx n) ω| := by
    intro ω
    by_cases h : ∃ k ≤ n, lam < g (idx k) ω
    · have hmem : ω ∈ A := h
      rw [Set.indicator_of_mem hmem]
      have hσ : σ ω = Nat.find h := by simp only [σ, dif_pos h]
      have := (Nat.find_spec h).2
      simp only [gs, hσ, Pi.one_apply, mul_one]
      linarith [abs_nonneg (g (idx n) ω)]
    · have hmem : ω ∉ A := h
      rw [Set.indicator_of_notMem hmem]
      have hσ : σ ω = n := by simp only [σ, dif_neg h]
      simp only [gs, hσ, mul_zero]
      linarith [neg_abs_le (g (idx n) ω)]
  have hE : ∫ ω, gs ω ∂μ ≤ K + ∫ ω, |g (idx 0) ω| ∂μ := by
    have : ∫ ω, gs ω ∂μ = ∫ ω, (∑ k ∈ range n, W k ω * (g (idx (k + 1)) ω - g (idx k) ω)) ∂μ
        + ∫ ω, g (idx 0) ω ∂μ := by
      rw [← integral_add hint_sum (hgint _)]
      congr 1; funext ω; rw [htel]; ring
    rw [this]
    have := integral_mono (hgint (idx 0)) (hgint (idx 0)).abs fun ω => le_abs_self (g (idx 0) ω)
    linarith
  calc lam * μ.real A = ∫ ω, lam * A.indicator 1 ω ∂μ := by
        rw [integral_const_mul, integral_indicator_one hAm]
    _ ≤ ∫ ω, (gs ω + |g (idx n) ω|) ∂μ :=
        integral_mono (((integrable_const (1 : ℝ)).indicator hAm).const_mul lam)
          (hgs.add (hgint _).abs) hpt
    _ = ∫ ω, gs ω ∂μ + ∫ ω, |g (idx n) ω| ∂μ := integral_add hgs (hgint _).abs
    _ ≤ K + ∫ ω, |g (idx 0) ω| ∂μ + ∫ ω, |g (idx n) ω| ∂μ := by linarith

end Maximal

end ProbabilityTheory
