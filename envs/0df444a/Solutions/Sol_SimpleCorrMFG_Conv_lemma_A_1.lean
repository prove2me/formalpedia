-- Prove2me | solution 1 for SimpleCorrMFG.Conv.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T06:26:53.048648+00:00
-- url     : https://prove2.me/submissions/07515fdb-e618-4055-af16-a0fa1596e276

import Mathlib

open MeasureTheory ProbabilityTheory unitInterval Filter Topology

theorem solution {𝒴 𝒵 : Type*} [TopologicalSpace 𝒴] [PolishSpace 𝒴] [MeasurableSpace 𝒴] [BorelSpace 𝒴]
    [TopologicalSpace 𝒵] [PolishSpace 𝒵] [MeasurableSpace 𝒵] [BorelSpace 𝒵]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)]
    (Yn : ∀ n, Ω n → 𝒴) (Zn : ∀ n, Ω n → 𝒵) (hYn : ∀ n, Measurable (Yn n))
    (hZn : ∀ n, Measurable (Zn n))
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → 𝒴) (Z : Ω' → 𝒵) (hY : Measurable Y) (hZ : Measurable Z)
    (Ψ : 𝒵 → 𝒴) (hΨ : Measurable Ψ)
    (hconv : TendstoInDistribution (fun n ω => (Yn n ω, Zn n ω)) atTop (fun ω => (Y ω, Z ω)) P P')
    (hYΨ : ∀ n, Yn n =ᵐ[P n] (Ψ ∘ Zn n))
    (hcont : ∀ᵐ z ∂(P'.map Z), ContinuousAt Ψ z) :
    Y =ᵐ[P'] (Ψ ∘ Z) := by
  -- the closure of the graph of `Ψ`
  set G : Set (𝒴 × 𝒵) := closure {p | p.1 = Ψ p.2} with hG
  have hGc : IsClosed G := isClosed_closure
  have hGm : MeasurableSet G := hGc.measurableSet
  have hmn : ∀ n, Measurable (fun ω => (Yn n ω, Zn n ω)) := fun n => (hYn n).prodMk (hZn n)
  have hm : Measurable (fun ω => (Y ω, Z ω)) := hY.prodMk hZ
  -- every approximating law gives full mass to `G`
  have hn : ∀ n, ((P n).map (fun ω => (Yn n ω, Zn n ω))) G = 1 := by
    intro n
    rw [Measure.map_apply (hmn n) hGm]
    have : ∀ᵐ ω ∂(P n), ω ∈ (fun ω => (Yn n ω, Zn n ω)) ⁻¹' G := by
      filter_upwards [hYΨ n] with ω hω
      exact subset_closure (show (Yn n ω, Zn n ω).1 = Ψ (Yn n ω, Zn n ω).2 from hω)
    rw [← measure_univ (μ := P n)]
    refine measure_congr (ae_eq_univ.mpr ?_)
    rw [ae_iff] at this
    exact this
  have hlim := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hconv.tendsto hGc
  simp only [ProbabilityMeasure.coe_mk, hn] at hlim
  rw [limsup_const] at hlim
  -- hence the limit law gives full mass to `G`
  have hfull : ∀ᵐ ω ∂P', (Y ω, Z ω) ∈ G := by
    have h1 : (P'.map (fun ω => (Y ω, Z ω))) G = 1 := le_antisymm prob_le_one hlim
    rw [Measure.map_apply hm hGm] at h1
    rw [ae_iff]
    have h2 : P' ((fun ω => (Y ω, Z ω)) ⁻¹' G)ᶜ = 0 := by
      rw [prob_compl_eq_zero_iff (hm hGm)]; exact h1
    exact h2
  have hcont' : ∀ᵐ ω ∂P', ContinuousAt Ψ (Z ω) := ae_of_ae_map hZ.aemeasurable hcont
  filter_upwards [hfull, hcont'] with ω h1 h2
  -- a point of the closure of the graph at which `Ψ` is continuous lies on the graph
  show Y ω = Ψ (Z ω)
  have hcl : ContinuousAt (fun p : 𝒴 × 𝒵 => (p.1, Ψ p.2)) (Y ω, Z ω) :=
    continuousAt_fst.prodMk (ContinuousAt.comp (f := Prod.snd) (x := (Y ω, Z ω)) h2 continuousAt_snd)
  have hdiag : IsClosed {q : 𝒴 × 𝒴 | q.1 = q.2} := isClosed_diagonal
  by_contra hne
  have hopen : IsOpen {q : 𝒴 × 𝒴 | q.1 = q.2}ᶜ := hdiag.isOpen_compl
  have hmem : (Y ω, Ψ (Z ω)) ∈ {q : 𝒴 × 𝒴 | q.1 = q.2}ᶜ := hne
  obtain ⟨U, hU, hUsub⟩ : ∃ U ∈ 𝓝 (Y ω, Z ω), ∀ p ∈ U, (p.1, Ψ p.2) ∈ {q : 𝒴 × 𝒴 | q.1 = q.2}ᶜ :=
    ⟨_, hcl (hopen.mem_nhds hmem), fun p hp => hp⟩
  obtain ⟨p, hpU, hpG⟩ := mem_closure_iff_nhds.mp h1 U hU
  exact hUsub p hpU hpG
