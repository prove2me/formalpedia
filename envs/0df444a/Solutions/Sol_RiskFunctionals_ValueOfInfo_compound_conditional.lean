-- Prove2me | solution 1 for RiskFunctionals.ValueOfInfo.compound_conditional
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:41:08.528295+00:00
-- url     : https://prove2.me/submissions/4496e812-bf3b-4cc3-828a-b24104dbbf3b

import Mathlib
import Definitions.Def_RiskFunctionals_ValueOfInfo_Compounding

open RiskFunctionals.ValueOfInfo

open MeasureTheory ProbabilityTheory

theorem g79t_cc_core {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] (hm : m ≤ mΩ) (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : Measurable Y) :
    ∃ (G : Measure ℝ) (_ : IsProbabilityMeasure G) (K : Kernel ℝ ℝ) (_ : IsMarkovKernel K),
      K ∘ₘ G = P.map Y ∧
      (∀ (p : Measure ℝ → Prop), (∀ᵐ y ∂G, p (K y)) ↔ ∀ᵐ ω ∂P, p ((condExpKernel P m ω).map Y)) ∧
      (∀ g : Measure ℝ → ℝ, (Integrable (fun y => g (K y)) G ↔
          Integrable (fun ω => g ((condExpKernel P m ω).map Y)) P) ∧
        ∫ y, g (K y) ∂G = ∫ ω, g ((condExpKernel P m ω).map Y) ∂P) := by
  obtain ⟨e, he⟩ := @exists_measurableEmbedding_real Ω mΩ _
  have hne : Nonempty Ω := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := measure_univ (μ := P)
    rw [Set.univ_eq_empty_iff.mpr h, measure_empty] at this
    exact zero_ne_one this
  obtain ⟨r, hr, hre⟩ := he.exists_measurable_extend (measurable_id) (fun _ => hne)
  have hre' : ∀ ω, r (e ω) = ω := fun ω => congrFun hre ω
  set κ := condExpKernel P m
  let K : Kernel ℝ ℝ := Kernel.comap (Kernel.map κ Y) r (hr.mono le_rfl hm)
  have hK : ∀ y, K y = (κ (r y)).map Y := fun y => by
    simp only [K, Kernel.comap_apply, Kernel.map_apply _ hY]
  have hKe : ∀ ω, K (e ω) = (κ ω).map Y := fun ω => by rw [hK, hre']
  haveI : IsMarkovKernel K := by
    simp only [K]
    haveI : IsMarkovKernel (Kernel.map κ Y) := Kernel.IsMarkovKernel.map κ hY
    infer_instance
  refine ⟨P.map e, Measure.isProbabilityMeasure_map he.measurable.aemeasurable, K, inferInstance,
    ?_, ?_, ?_⟩
  · ext s hs
    rw [Measure.bind_apply hs K.aemeasurable, lintegral_map (K.measurable_coe hs) he.measurable,
      Measure.map_apply hY hs]
    simp_rw [hKe, Measure.map_apply hY hs]
    have hmeas : Measurable[m] (fun ω => κ ω (Y ⁻¹' s)) := κ.measurable_coe (hY hs)
    rw [← lintegral_trim hm hmeas, ← Measure.bind_apply (hY hs) κ.aemeasurable]
    change (κ ∘ₘ P.trim hm) (Y ⁻¹' s) = _
    rw [condExpKernel_comp_trim hm]
  · intro p
    rw [he.ae_map_iff]
    simp_rw [hKe]
  · intro g
    constructor
    · rw [he.integrable_map_iff]
      constructor <;> intro h <;> convert h using 2 <;> simp [Function.comp, hKe]
    · rw [he.integral_map]
      simp_rw [hKe]

theorem solution {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] (hm : m ≤ mΩ) (P : Measure Ω) [IsProbabilityMeasure P]
    (𝒟 : Set (Measure ℝ)) (ℛ : Measure ℝ → ℝ) (Y : Ω → ℝ) (hY : Measurable Y)
    (hYdom : P.map Y ∈ 𝒟) (hconddom : ∀ᵐ ω ∂P, (condExpKernel P m ω).map Y ∈ 𝒟)
    (hint : Integrable (fun ω => ℛ ((condExpKernel P m ω).map Y)) P) :
    (CompoundLinear 𝒟 ℛ → ℛ (P.map Y) = ∫ ω, ℛ ((condExpKernel P m ω).map Y) ∂P) ∧
    (CompoundConvex 𝒟 ℛ → ℛ (P.map Y) ≤ ∫ ω, ℛ ((condExpKernel P m ω).map Y) ∂P) ∧
    (CompoundConcave 𝒟 ℛ → ∫ ω, ℛ ((condExpKernel P m ω).map Y) ∂P ≤ ℛ (P.map Y)) := by
  obtain ⟨G, hG, K, hK, hcomp, hae, hint'⟩ := g79t_cc_core m hm P Y hY
  have h1 : ∀ᵐ v ∂G, K v ∈ 𝒟 := (hae (· ∈ 𝒟)).2 hconddom
  have h2 : K ∘ₘ G ∈ 𝒟 := hcomp ▸ hYdom
  have h3 : Integrable (fun v => ℛ (K v)) G := ((hint' ℛ).1).2 hint
  have h4 := (hint' ℛ).2
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := h G hG K hK h1 h2 h3; rw [hcomp, h4] at this; exact this
  · have := h G hG K hK h1 h2 h3; rw [hcomp, h4] at this; exact this
  · have := h G hG K hK h1 h2 h3; rw [hcomp, h4] at this; exact this
