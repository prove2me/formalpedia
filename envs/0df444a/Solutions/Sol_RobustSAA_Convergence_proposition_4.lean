-- Prove2me | solution 1 for RobustSAA.Convergence.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T20:01:11.492252+00:00
-- url     : https://prove2.me/submissions/90e7d787-216d-4e02-8e69-77392859a6e0

import Mathlib
import Definitions.Def_RobustSAA_Convergence_Consistency

open MeasureTheory Filter Topology
open scoped ENNReal
open RobustSAA.Convergence

theorem solution {d : ℕ} {Ξ : Set (Pt d)} (𝓕 : DUS Ξ)
    (hne : ∀ (N : ℕ) (s : Fin N → ↥Ξ), (𝓕 N s).Nonempty)
    (hmeas : ∀ (N : ℕ) (F₀ : ProbabilityMeasure ↥Ξ),
      MeasurableSet {s : Fin N → ↥Ξ | F₀ ∉ 𝓕 N s})
    (h𝓕 : IsUniformlyConsistent 𝓕) :
    IsConsistent 𝓕 := by
  classical
  intro F F₀ hF₀
  -- a.s., `F₀` is eventually rejected
  have hev : ∀ᵐ ω ∂(dataLaw F), ∀ᶠ N in atTop, F₀ ∉ 𝓕 N (sample ω N) := by
    filter_upwards [h𝓕 F] with ω hω
    by_contra hfr
    rw [not_eventually] at hfr
    simp only [not_not] at hfr
    let G : ℕ → ProbabilityMeasure ↥Ξ := fun N =>
      if F₀ ∈ 𝓕 N (sample ω N) then F₀ else (hne N (sample ω N)).some
    have hGmem : ∀ N, G N ∈ 𝓕 N (sample ω N) := by
      intro N
      by_cases h : F₀ ∈ 𝓕 N (sample ω N)
      · simp only [G, if_pos h]; exact h
      · simp only [G, if_neg h]; exact (hne N (sample ω N)).some_mem
    have hnt : ¬ Tendsto G atTop (𝓝 F) := by
      intro hT
      have h1 : ∀ᶠ N in atTop, G N ∈ ({F₀}ᶜ : Set (ProbabilityMeasure ↥Ξ)) :=
        hT (isOpen_compl_singleton.mem_nhds (by simpa [eq_comm] using hF₀))
      obtain ⟨N, hN1, hN2⟩ := (hfr.and_eventually h1).exists
      apply hN2
      simp only [G, if_pos hN1, Set.mem_singleton_iff]
    obtain ⟨N, hN⟩ := (hω G hnt).exists
    exact hN (hGmem N)
  have hmeasA : ∀ N, MeasurableSet {ω : ℕ → ↥Ξ | F₀ ∉ 𝓕 N (sample ω N)} := by
    intro N
    have hm : Measurable (fun ω : ℕ → ↥Ξ => sample ω N) :=
      measurable_pi_lambda _ (fun i => measurable_pi_apply (i : ℕ))
    exact hm (hmeas N F₀)
  have hprob : IsProbabilityMeasure (dataLaw F) := by
    unfold dataLaw; infer_instance
  have := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure (μ := dataLaw F)
    (L := atTop) (A := Set.univ) MeasurableSet.univ hmeasA
    (by filter_upwards [hev] with ω hω; filter_upwards [hω] with N hN; simp [hN])
  simpa [measure_univ] using this
