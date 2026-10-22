-- Prove2me | solution 1 for SmithHitAndRun.SymMixing.lemma_2_indecomposable
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T05:47:30.358244+00:00
-- url     : https://prove2.me/submissions/e62921e5-a819-4b5a-ba1e-4d9cb865cea2

import Mathlib.Probability.Kernel.Invariance
import Definitions.Def_MarkovIterKernel
import Definitions.Def_SmithHitAndRun_SymMixing_IsSymmetricMixingKernel
import Definitions.Def_SmithHitAndRun_SymMixing_IsClosedSet

open MeasureTheory ProbabilityTheory


namespace SmithHitAndRun.SymMixing

theorem key_pos {α : Type*} [MeasurableSpace α]
    (V : Measure α) [IsFiniteMeasure V]
    (P : Kernel α α) [IsMarkovKernel P] (f : α → α → ENNReal)
    (h : IsSymmetricMixingKernel V P f) (hpos : ∀ x y, 0 < f y x)
    (B : Set α) (hB : MeasurableSet B) (hVB : V B ≠ 0) (z : α) : 0 < P z B := by
  obtain ⟨hf, hP, hsym⟩ := h
  rw [pos_iff_ne_zero]
  intro h0
  rw [hP z B hB] at h0
  have hm : Measurable (fun y => f y z) := by
    have : Measurable (fun y => Function.uncurry f (y, z)) :=
      hf.comp (measurable_id.prodMk measurable_const)
    exact this
  rw [lintegral_eq_zero_iff hm] at h0
  have h2 : ∀ᵐ y ∂(V.restrict B), False :=
    h0.mono (fun y hy => by have := hpos z y; simp only [Pi.zero_apply] at hy; rw [hy] at this; exact lt_irrefl _ this)
  simp only [Filter.eventually_false_iff_eq_bot, ae_eq_bot, Measure.restrict_eq_zero] at h2
  exact hVB h2

theorem key_pos_iter {α : Type*} [MeasurableSpace α]
    (V : Measure α) [IsFiniteMeasure V]
    (P : Kernel α α) [IsMarkovKernel P] (f : α → α → ENNReal)
    (h : IsSymmetricMixingKernel V P f) (hpos : ∀ x y, 0 < f y x)
    (B : Set α) (hB : MeasurableSet B) (hVB : V B ≠ 0) (n : ℕ) (x : α) :
    0 < MarkovChainCLT.iterKernel P (n + 1) x B := by
  rw [MarkovChainCLT.iterKernel_succ, Kernel.comp_apply' _ _ _ hB]
  rw [pos_iff_ne_zero]
  intro h0
  rw [lintegral_eq_zero_iff (Kernel.measurable_coe P hB)] at h0
  have h2 : ∀ᵐ z ∂(MarkovChainCLT.iterKernel P n x), False :=
    h0.mono (fun z hz => by
      have := key_pos V P f h hpos B hB hVB z
      simp only [Pi.zero_apply] at hz; rw [hz] at this; exact lt_irrefl _ this)
  simp only [Filter.eventually_false_iff_eq_bot, ae_eq_bot] at h2
  exact (IsProbabilityMeasure.ne_zero _) h2

theorem closed_null {α : Type*} [MeasurableSpace α]
    (V : Measure α) [IsFiniteMeasure V]
    (P : Kernel α α) [IsMarkovKernel P] (f : α → α → ENNReal)
    (h : IsSymmetricMixingKernel V P f) (hpos : ∀ x y, 0 < f y x)
    (n : ℕ) (A : Set α) (hA : IsClosedSet (MarkovChainCLT.iterKernel P (n + 1)) A) :
    V Aᶜ = 0 := by
  obtain ⟨⟨x, hx⟩, hAm, hc⟩ := hA
  by_contra hne
  have := key_pos_iter V P f h hpos Aᶜ hAm.compl hne n x
  have h0 : MarkovChainCLT.iterKernel P (n + 1) x Aᶜ = 0 :=
    (prob_compl_eq_zero_iff hAm).2 (hc x hx)
  rw [h0] at this
  exact lt_irrefl _ this

theorem no_two_closed {α : Type*} [MeasurableSpace α]
    (V : Measure α) [IsFiniteMeasure V] (hV : V ≠ 0)
    (P : Kernel α α) [IsMarkovKernel P] (f : α → α → ENNReal)
    (h : IsSymmetricMixingKernel V P f) (hpos : ∀ x y, 0 < f y x)
    (n : ℕ) :
    ¬ ∃ A₁ A₂ : Set α,
        IsClosedSet (MarkovChainCLT.iterKernel P (n + 1)) A₁ ∧
        IsClosedSet (MarkovChainCLT.iterKernel P (n + 1)) A₂ ∧ A₁ ∩ A₂ = ∅ := by
  rintro ⟨A₁, A₂, h1, h2, hd⟩
  have e1 := closed_null V P f h hpos n A₁ h1
  have e2 := closed_null V P f h hpos n A₂ h2
  apply hV
  rw [← Measure.measure_univ_eq_zero]
  have : (Set.univ : Set α) ⊆ A₁ᶜ ∪ A₂ᶜ := by
    intro x _
    by_cases hx : x ∈ A₁
    · right; intro hx2; have : x ∈ A₁ ∩ A₂ := ⟨hx, hx2⟩; rw [hd] at this; exact this
    · left; exact hx
  exact le_antisymm ((measure_mono this).trans ((measure_union_le _ _).trans (by simp [e1, e2]))) bot_le

theorem lemma2_core {α : Type*} [MeasurableSpace α]
    (V : Measure α) [IsFiniteMeasure V] (hV : V ≠ 0)
    (P : Kernel α α) [IsMarkovKernel P] (f : α → α → ENNReal)
    (h : IsSymmetricMixingKernel V P f) (hpos : ∀ x y, 0 < f y x) :
    ¬ ∃ A₁ A₂ : Set α,
      IsClosedSet P A₁ ∧ IsClosedSet P A₂ ∧ A₁ ∩ A₂ = ∅ := by
  have := no_two_closed V hV P f h hpos 0
  have e : MarkovChainCLT.iterKernel P 1 = P := by
    simp [MarkovChainCLT.iterKernel_succ]
  rw [e] at this
  exact this

theorem nstep_core {α : Type*} [MeasurableSpace α]
    (V : Measure α) [IsFiniteMeasure V] (hV : V ≠ 0)
    (P : Kernel α α) [IsMarkovKernel P] (f : α → α → ENNReal)
    (h : IsSymmetricMixingKernel V P f) (hpos : ∀ x y, 0 < f y x) :
    ∀ n : ℕ, 2 ≤ n →
      ¬ ∃ A₁ A₂ : Set α,
        IsClosedSet (MarkovChainCLT.iterKernel P n) A₁ ∧
        IsClosedSet (MarkovChainCLT.iterKernel P n) A₂ ∧ A₁ ∩ A₂ = ∅ := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact no_two_closed V hV P f h hpos m

end SmithHitAndRun.SymMixing

open SmithHitAndRun.SymMixing


theorem solution {α : Type*} [MeasurableSpace α]
    (V : Measure α) [IsFiniteMeasure V] (hV : V ≠ 0)
    (P : Kernel α α) [IsMarkovKernel P] (f : α → α → ENNReal)
    (h : IsSymmetricMixingKernel V P f) (hpos : ∀ x y, 0 < f y x) :
    ¬ ∃ A₁ A₂ : Set α,
      IsClosedSet P A₁ ∧ IsClosedSet P A₂ ∧ A₁ ∩ A₂ = ∅ := by
  exact lemma2_core V hV P f h hpos
