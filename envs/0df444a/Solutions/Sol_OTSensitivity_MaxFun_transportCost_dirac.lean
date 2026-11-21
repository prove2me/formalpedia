-- Prove2me | solution 1 for OTSensitivity.MaxFun.transportCost_dirac
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-21T03:32:25.710869+00:00
-- url     : https://prove2.me/submissions/1f3439de-7652-4dc2-8793-38e4fd45e84a

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_OTSensitivity_MaxFun_Setting

open MeasureTheory ProbabilityTheory OTSensitivity.MaxFun
open scoped ENNReal

theorem solution {𝒴 : Type*} [TopologicalSpace 𝒴] [PolishSpace 𝒴] [MeasurableSpace 𝒴]
    [BorelSpace 𝒴] (k : 𝒴 → 𝒴 → ℝ≥0∞) (hk : IsCost k)
    (ν : Measure 𝒴) [IsProbabilityMeasure ν] (y' : 𝒴) :
    RWPI.SqrtLasso.transportCost k ν (Measure.dirac y') = ∫⁻ y, k y y' ∂ν := by
  let f : 𝒴 → 𝒴 × 𝒴 := fun y => (y, y')
  have hf : Measurable f := measurable_id.prodMk measurable_const
  have hcost : Measurable (fun y => k y y') := hk.1.measurable.comp hf
  have common (π : Measure (𝒴 × 𝒴))
      (hπ : IsProbabilityMeasure π ∧ π.map Prod.fst = ν ∧ π.map Prod.snd = Measure.dirac y') :
      (∫⁻ w, k w.1 w.2 ∂π) = ∫⁻ y, k y y' ∂ν := by
    have hs : ∀ᵐ w ∂π, w.2 = y' := by
      rw [ae_iff]
      change π (Prod.snd ⁻¹' ({y'} : Set 𝒴)ᶜ) = 0
      rw [← Measure.map_apply measurable_snd (MeasurableSet.singleton y').compl, hπ.2.2]
      simp
    calc
      (∫⁻ w, k w.1 w.2 ∂π) = ∫⁻ w, k w.1 y' ∂π :=
        lintegral_congr_ae (hs.mono fun w hw => congrArg (k w.1) hw)
      _ = ∫⁻ y, k y y' ∂ν := by
        rw [← hπ.2.1, lintegral_map hcost measurable_fst]
  have hmap : IsProbabilityMeasure (ν.map f) := by
    refine ⟨?_⟩
    rw [Measure.map_apply hf MeasurableSet.univ]
    simp
  have hfst : (ν.map f).map Prod.fst = ν := by
    rw [Measure.map_map measurable_fst hf]
    change ν.map id = ν
    simp
  have hsnd : (ν.map f).map Prod.snd = Measure.dirac y' := by
    rw [Measure.map_map measurable_snd hf]
    change ν.map (fun _ => y') = Measure.dirac y'
    ext s hs
    rw [Measure.map_apply measurable_const hs, Measure.dirac_apply' _ hs]
    by_cases h : y' ∈ s <;> simp [Set.preimage, h]
  unfold RWPI.SqrtLasso.transportCost
  apply le_antisymm
  · have hπ := And.intro hmap (And.intro hfst hsnd)
    exact (iInf_le_of_le (ν.map f) (iInf_le _ hπ)).trans_eq (common _ hπ)
  · exact le_iInf fun π => le_iInf fun hπ => (common π hπ).ge
