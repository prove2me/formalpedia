-- Prove2me | solution 1 for ProcessingNetworks.Stability.processing_variable_slln
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:57:22.52364+00:00
-- url     : https://prove2.me/submissions/af5b9cf2-1790-4814-b534-49975f016ea2

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_BaselineAssumptions

open ProcessingNetworks.Stability MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

theorem solution {Ω : Type*} [MeasureSpace Ω] {I J : ℕ} {N0 : Fin J → ℕ}
    {E : Fin I → ℝ → Ω → ℕ} {lam : Fin I → ℝ≥0}
    {v : Fin J → ℕ → Ω → ℝ} {φ : Fin J → ℕ → Ω → Fin I → ℕ}
    {m : Fin J → ℝ} {Γ : Fin J → Fin I → ℝ} {Psi : Fin J → ℕ → Ω → ℝ × (Fin I → ℕ)}
    (h : BaselineAssumptions I J N0 E lam v φ m Γ Psi) (j : Fin J) :
    ℙ {ω | Tendsto (fun n : ℕ => (∑ ℓ ∈ Finset.range n, v j ℓ ω) / n) atTop (nhds (m j)) ∧
           ∀ i : Fin I, Tendsto (fun n : ℕ => (∑ ℓ ∈ Finset.range n, (φ j ℓ ω i : ℝ)) / n)
             atTop (nhds (Γ j i))} = 1 := by
  have core := h.toCoreStochasticAssumptions
  have hiid := core.processing_iid j
  have hmean := core.mean_service_time j
  have hvpos := core.processing_positive j
  set f : ℕ → Ω → ℝ × (Fin I → ℕ) := fun ℓ ω => (v j ℓ ω, φ j ℓ ω) with hf
  have hind01 : IndepFun (f 0) (f 1) ℙ := hiid.1.indepFun (by norm_num)
  have key : ∀ s : Set (ℝ × (Fin I → ℕ)), MeasurableSet s →
      ℙ (f 0 ⁻¹' s) = ℙ (f 0 ⁻¹' s) * ℙ (Set.univ : Set Ω) := by
    intro s hs
    have := hind01.measure_inter_preimage_eq_mul s Set.univ hs MeasurableSet.univ
    simpa using this
  have hprob : IsProbabilityMeasure (ℙ : Measure Ω) := by
    constructor
    have huniv : ℙ (Set.univ : Set Ω) = ℙ (Set.univ : Set Ω) * ℙ (Set.univ : Set Ω) := by
      simpa using key Set.univ MeasurableSet.univ
    have h0 : ℙ (Set.univ : Set Ω) ≠ 0 := by
      intro h0
      have hμ : (ℙ : Measure Ω) = 0 := Measure.measure_univ_eq_zero.mp h0
      have := hmean.2.1
      rw [hμ, integral_zero_measure] at this
      linarith [hmean.2.2]
    have htop : ℙ (Set.univ : Set Ω) ≠ ⊤ := by
      intro htop
      have hA : ∀ n : ℕ, ℙ {ω | ((n : ℝ) + 1)⁻¹ < v j 0 ω} = 0 := by
        intro n
        set c : ℝ := ((n : ℝ) + 1)⁻¹ with hc
        have hcpos : 0 < c := by positivity
        have hs : MeasurableSet {p : ℝ × (Fin I → ℕ) | c < p.1} :=
          measurableSet_lt measurable_const measurable_fst
        have hk := key _ hs
        have hpre : f 0 ⁻¹' {p : ℝ × (Fin I → ℕ) | c < p.1} = {ω | c < v j 0 ω} := rfl
        rw [hpre, htop] at hk
        -- finiteness by Markov
        have hfin : ℙ {ω | c < v j 0 ω} ≠ ⊤ := by
          have hlint : ∫⁻ ω, ENNReal.ofReal (v j 0 ω) ∂ℙ < ⊤ := by
            have := hmean.1.2
            refine lt_of_le_of_lt (le_of_eq ?_) this
            refine lintegral_congr fun ω => ?_
            rw [Real.enorm_eq_ofReal_abs, abs_of_pos (hvpos 0 ω)]
          have hmk := mul_meas_ge_le_lintegral₀ (μ := ℙ)
            (hmean.1.aemeasurable.ennreal_ofReal) (ENNReal.ofReal c)
          have hsub : {ω | c < v j 0 ω} ⊆ {ω | ENNReal.ofReal c ≤ ENNReal.ofReal (v j 0 ω)} :=
            fun ω hω => ENNReal.ofReal_le_ofReal hω.le
          intro hT
          have : ENNReal.ofReal c * ℙ {ω | ENNReal.ofReal c ≤ ENNReal.ofReal (v j 0 ω)} = ⊤ := by
            have h2 : ℙ {ω | ENNReal.ofReal c ≤ ENNReal.ofReal (v j 0 ω)} = ⊤ :=
              top_unique (by rw [← hT]; exact measure_mono hsub)
            rw [h2]
            exact ENNReal.mul_top (by simpa using hcpos)
          rw [this] at hmk
          exact absurd (lt_of_le_of_lt hmk hlint) (lt_irrefl _)
        by_contra hne
        rw [ENNReal.mul_top hne] at hk
        exact hfin hk
      have hU : (Set.univ : Set Ω) = ⋃ n : ℕ, {ω | ((n : ℝ) + 1)⁻¹ < v j 0 ω} := by
        ext ω
        simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_setOf_eq, true_iff]
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (hvpos 0 ω)
        exact ⟨n, by simpa [one_div] using hn⟩
      have : ℙ (Set.univ : Set Ω) = 0 := by
        rw [hU]; exact measure_iUnion_null hA
      exact h0 this
    have hx := huniv
    rcases eq_or_ne (ℙ (Set.univ : Set Ω)) 1 with h1 | h1
    · exact h1
    · exfalso
      have : ℙ (Set.univ : Set Ω) * 1 = ℙ (Set.univ : Set Ω) * ℙ (Set.univ : Set Ω) := by
        rw [mul_one]; exact hx
      exact h1 ((ENNReal.mul_right_inj h0 htop).mp this).symm
  -- SLLN for the service times
  have hv : ∀ᵐ ω ∂ℙ, Tendsto (fun n : ℕ => (∑ ℓ ∈ Finset.range n, v j ℓ ω) / n) atTop
      (nhds (m j)) := by
    have := strong_law_ae_real (μ := ℙ) (fun ℓ => v j ℓ) hmean.1
      (fun a b hab => (hiid.1.comp (fun _ => Prod.fst) (fun _ => measurable_fst)).indepFun hab)
      (fun ℓ => (hiid.2 ℓ).comp measurable_fst)
    rwa [hmean.2.1] at this
  have hphi : ∀ i : Fin I, ∀ᵐ ω ∂ℙ, Tendsto (fun n : ℕ => (∑ ℓ ∈ Finset.range n,
      (φ j ℓ ω i : ℝ)) / n) atTop (nhds (Γ j i)) := by
    intro i
    have hm : Measurable (fun p : ℝ × (Fin I → ℕ) => ((p.2 i : ℕ) : ℝ)) :=
      measurable_from_top.comp ((measurable_pi_apply i).comp measurable_snd)
    have := strong_law_ae_real (μ := ℙ) (fun ℓ ω => (φ j ℓ ω i : ℝ)) (core.mean_output j i).1
      (fun a b hab => (hiid.1.comp (fun _ => fun p : ℝ × (Fin I → ℕ) => ((p.2 i : ℕ) : ℝ))
        (fun _ => hm)).indepFun hab)
      (fun ℓ => (hiid.2 ℓ).comp hm)
    rwa [(core.mean_output j i).2.1] at this
  have hall : ∀ᵐ ω ∂ℙ, Tendsto (fun n : ℕ => (∑ ℓ ∈ Finset.range n, v j ℓ ω) / n) atTop
      (nhds (m j)) ∧ ∀ i : Fin I, Tendsto (fun n : ℕ => (∑ ℓ ∈ Finset.range n,
        (φ j ℓ ω i : ℝ)) / n) atTop (nhds (Γ j i)) :=
    hv.and (ae_all_iff.mpr hphi)
  refine le_antisymm prob_le_one ?_
  set S := {ω : Ω | Tendsto (fun n : ℕ => (∑ ℓ ∈ Finset.range n, v j ℓ ω) / n) atTop (nhds (m j)) ∧
           ∀ i : Fin I, Tendsto (fun n : ℕ => (∑ ℓ ∈ Finset.range n, (φ j ℓ ω i : ℝ)) / n)
             atTop (nhds (Γ j i))} with hS
  have h0 : ℙ Sᶜ = 0 := by rw [hS, Set.compl_setOf]; exact ae_iff.mp hall
  calc (1 : ℝ≥0∞) = ℙ (Set.univ : Set Ω) := measure_univ.symm
    _ ≤ ℙ S + ℙ Sᶜ := measure_univ_le_add_compl S
    _ = ℙ S := by rw [h0, add_zero]


