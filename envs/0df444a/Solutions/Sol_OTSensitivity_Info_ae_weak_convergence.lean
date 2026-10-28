-- Prove2me | solution 1 for OTSensitivity.Info.ae_weak_convergence
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T16:32:33.521796+00:00
-- url     : https://prove2.me/submissions/14c10c9f-f905-4dde-bdb6-6be53cb634fd

import Mathlib
import Definitions.Def_OTSensitivity_Info_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

open OTSensitivity.Info in
theorem solution {Ω 𝓧 𝓨 : Type*} [MeasurableSpace Ω] (Fs : ℕ → MeasurableSpace 𝓧)
    [TopologicalSpace 𝓧] [PolishSpace 𝓧] [m𝓧 : MeasurableSpace 𝓧] [BorelSpace 𝓧]
    [TopologicalSpace 𝓨] [PolishSpace 𝓨] [MeasurableSpace 𝓨] [BorelSpace 𝓨]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → 𝓧) (Y : Ω → 𝓨) (hX : Measurable X) (hY : Measurable Y)
    (hmono : Monotone Fs) (hle : ∀ n, Fs n ≤ m𝓧)
    (κs : ℕ → Kernel 𝓧 𝓨) (hκs : ∀ n, IsCondDistrib P X Y (Fs n) (κs n))
    (κ : Kernel 𝓧 𝓨) (hκ : IsCondDistrib P X Y (⨆ n, Fs n) κ) :
    ∀ᵐ x ∂(P.map X), ∀ φ : 𝓨 →ᵇ ℝ,
      Tendsto (fun n => ∫ y, φ y ∂(κs n x)) atTop (𝓝 (∫ y, φ y ∂(κ x))) := by
  classical
  set μ : Measure 𝓧 := P.map X with hμdef
  haveI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hX.aemeasurable
  have hM : ∀ n, IsMarkovKernel (κs n) := fun n => (hκs n).1
  haveI : IsMarkovKernel κ := hκ.1
  have hFsup : (⨆ n, Fs n) ≤ m𝓧 := iSup_le hle
  -- Step 1: setwise a.e. convergence via Lévy's upward theorem
  have key : ∀ B : Set 𝓨, MeasurableSet B →
      ∀ᵐ x ∂μ, Tendsto (fun n => κs n x B) atTop (𝓝 (κ x B)) := by
    intro B hB
    let f : 𝓧 → ℝ := fun x => (κ x B).toReal
    have hfm' : Measurable[⨆ n, Fs n] (fun x => κ x B) := hκ.2.1 B hB
    have hfsm : StronglyMeasurable[⨆ n, Fs n] f := hfm'.ennreal_toReal.stronglyMeasurable
    have hbound : ∀ (η : Kernel 𝓧 𝓨) [IsMarkovKernel η], Integrable (fun x => (η x B).toReal) μ := by
      intro η _
      refine Integrable.of_bound ((η.measurable_coe hB).ennreal_toReal.aestronglyMeasurable) 1
        (Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
    have hfi : Integrable f μ := hbound κ
    have hcond : ∀ n, (fun x => (κs n x B).toReal) =ᵐ[μ] μ[f | Fs n] := by
      intro n
      haveI : IsMarkovKernel (κs n) := hM n
      haveI : IsFiniteMeasure (μ.trim (hle n)) := isFiniteMeasure_trim (hle n)
      refine ae_eq_condExp_of_forall_setIntegral_eq (hle n) hfi ?_ ?_ ?_
      · intro s _ _
        exact (hbound (κs n)).integrableOn
      · intro s hs _
        rw [integral_toReal ((κs n).measurable_coe hB).aemeasurable
            (Eventually.of_forall fun x => measure_lt_top _ _),
          integral_toReal (κ.measurable_coe hB).aemeasurable
            (Eventually.of_forall fun x => measure_lt_top _ _)]
        congr 1
        rw [← (hκs n).2.2 s hs B hB, ← hκ.2.2 s ((le_iSup Fs n) s hs) B hB]
      · exact ((hκs n).2.1 B hB).ennreal_toReal.stronglyMeasurable.aestronglyMeasurable
    let ℱ : Filtration ℕ m𝓧 := ⟨Fs, hmono, hle⟩
    have hlevy := tendsto_ae_condExp (μ := μ) (ℱ := ℱ) f
    have hsup : μ[f | ⨆ n, ℱ n] = f := condExp_of_stronglyMeasurable hFsup hfsm hfi
    filter_upwards [hlevy, ae_all_iff.2 hcond] with x hx hx2
    rw [hsup] at hx
    have h' : Tendsto (fun n => (κs n x B).toReal) atTop (𝓝 (κ x B).toReal) :=
      hx.congr' (Eventually.of_forall fun n => (hx2 n).symm)
    exact (ENNReal.tendsto_toReal_iff (fun n => measure_ne_top _ _) (measure_ne_top _ _)).1 h'
  -- Step 2: a countable family of open sets
  rcases isEmpty_or_nonempty 𝓨 with hE | hNE
  · refine Eventually.of_forall fun x => ?_
    exfalso
    have h1 : κ x Set.univ = 1 := measure_univ
    rw [Set.univ_eq_empty_iff.2 hE, measure_empty] at h1
    exact zero_ne_one h1
  obtain ⟨b, hbc, -, hb⟩ := TopologicalSpace.exists_countable_basis 𝓨
  have hbne : b.Nonempty := by
    obtain ⟨y⟩ := hNE
    obtain ⟨v, hv, -, -⟩ := hb.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    exact ⟨v, hv⟩
  obtain ⟨U, rfl⟩ := hbc.exists_eq_range hbne
  let C : Finset ℕ → Set 𝓨 := fun t => ⋃ i ∈ t, U i
  have hC : ∀ t, MeasurableSet (C t) := fun t =>
    Finset.measurableSet_biUnion t (fun i _ => (hb.isOpen ⟨i, rfl⟩).measurableSet)
  have hall : ∀ᵐ x ∂μ, ∀ t : Finset ℕ, Tendsto (fun n => κs n x (C t)) atTop (𝓝 (κ x (C t))) :=
    ae_all_iff.2 (fun t => key _ (hC t))
  filter_upwards [hall] with x hx
  let μs : ℕ → ProbabilityMeasure 𝓨 := fun n => ⟨κs n x, by haveI := hM n; infer_instance⟩
  let μl : ProbabilityMeasure 𝓨 := ⟨κ x, inferInstance⟩
  have hT : Tendsto μs atTop (𝓝 μl) := by
    refine tendsto_of_forall_isOpen_le_liminf_nat' (fun G hG => ?_)
    let D : ℕ → Set 𝓨 := fun m => C ((Finset.range m).filter (fun i => U i ⊆ G))
    have hDmono : Monotone D := by
      intro m m' h y hy
      simp only [D, C, Set.mem_iUnion, Finset.mem_filter, Finset.mem_range] at hy ⊢
      obtain ⟨i, ⟨him, hiG⟩, hyi⟩ := hy
      exact ⟨i, ⟨lt_of_lt_of_le him h, hiG⟩, hyi⟩
    have hDle : ∀ m, D m ⊆ G := by
      intro m y hy
      simp only [D, C, Set.mem_iUnion, Finset.mem_filter, Finset.mem_range] at hy
      obtain ⟨i, ⟨-, hiG⟩, hyi⟩ := hy
      exact hiG hyi
    have hDG : ⋃ m, D m = G := by
      apply Set.Subset.antisymm (Set.iUnion_subset hDle)
      intro y hy
      obtain ⟨v, ⟨i, rfl⟩, hyv, hvG⟩ := hb.exists_subset_of_mem_open hy hG
      simp only [D, C, Set.mem_iUnion, Finset.mem_filter, Finset.mem_range]
      exact ⟨i + 1, i, ⟨Nat.lt_succ_self i, hvG⟩, hyv⟩
    have h1 := tendsto_measure_iUnion_atTop (μ := κ x) hDmono
    rw [hDG] at h1
    refine le_of_tendsto' h1 (fun m => ?_)
    have h2 := hx ((Finset.range m).filter (fun i => U i ⊆ G))
    show κ x (D m) ≤ liminf (fun n => κs n x G) atTop
    rw [← h2.liminf_eq]
    exact liminf_le_liminf (Eventually.of_forall fun n => measure_mono (hDle m))
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at hT
  intro φ
  exact hT φ
