-- Prove2me | solution 1 for OnlineNRM.TSFixed.posterior_matching_finite_oracle_experiment
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:30:52.452247+00:00
-- url     : https://prove2.me/submissions/2fb14779-0c12-436f-a9a2-54b6d6fb6edb

import Definitions.Def_OnlineNRM_TSFixed_EntropyExperiment
import Mathlib

open MeasureTheory ProbabilityTheory OnlineNRM.TSFixed
open scoped BigOperators OnlineNRM.TSFixed
namespace S216NRM

theorem condExp_selfadj {Ω : Type*} {H : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (hH : H ≤ mΩ)
    {f Z : Ω → ℝ} (hf : Measurable f) (hZ : Measurable Z) {c c' : ℝ}
    (hfc : ∀ ω, |f ω| ≤ c) (hZc : ∀ ω, |Z ω| ≤ c') :
    ∫ ω, (P[f | H]) ω * Z ω ∂P = ∫ ω, f ω * (P[Z | H]) ω ∂P := by
  have gen : ∀ {f Z : Ω → ℝ} {c c' : ℝ}, Measurable f → Measurable Z → (∀ ω, |f ω| ≤ c) →
      (∀ ω, |Z ω| ≤ c') →
      ∫ ω, (P[f | H]) ω * Z ω ∂P = ∫ ω, (P[f | H]) ω * (P[Z | H]) ω ∂P := by
    intro f Z c c' hf hZ hfc hZc
    have hfi : Integrable f P := Integrable.of_bound hf.aestronglyMeasurable c
      (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hfc ω)
    have hZi : Integrable Z P := Integrable.of_bound hZ.aestronglyMeasurable c'
      (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hZc ω)
    have hint : Integrable (P[f | H] * Z) P :=
      integrable_condExp.mul_bdd hZ.aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hZc ω)
    rw [← integral_condExp hH (f := fun ω => (P[f | H]) ω * Z ω)]
    exact integral_congr_ae (condExp_mul_of_stronglyMeasurable_left stronglyMeasurable_condExp
      hint hZi)
  have h2 := gen hZ hf hZc hfc
  rw [gen hf hZ hfc hZc]
  calc ∫ ω, (P[f | H]) ω * (P[Z | H]) ω ∂P = ∫ ω, (P[Z | H]) ω * (P[f | H]) ω ∂P := by
        congr 1; funext ω; ring
    _ = ∫ ω, (P[Z | H]) ω * f ω ∂P := h2.symm
    _ = ∫ ω, f ω * (P[Z | H]) ω ∂P := by congr 1; funext ω; ring

theorem wd_apply {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : Ω → ℝ} (hZi : Integrable Z P) (hZ0 : 0 ≤ᵐ[P] Z)
    {S : Set Ω} (hS : MeasurableSet S) :
    P.withDensity (fun ω => ENNReal.ofReal (Z ω)) S
      = ENNReal.ofReal (∫ ω, S.indicator (fun _ => (1 : ℝ)) ω * Z ω ∂P) := by
  rw [withDensity_apply _ hS, ← ofReal_integral_eq_lintegral_ofReal hZi.integrableOn
    (ae_restrict_of_ae hZ0)]
  congr 1
  rw [← integral_indicator hS]
  congr 1; funext ω
  by_cases h : ω ∈ S <;> simp [h]

theorem transfer {Ω Θ : Type*} {H L : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace Θ] {P : Measure Ω}
    [IsProbabilityMeasure P] (hH : H ≤ mΩ) (hL : L ≤ mΩ)
    {X Y : Ω → Θ} (hX : Measurable X) (hY : Measurable Y)
    (hs : ∀ C : Set Θ, MeasurableSet C →
      P[(X ⁻¹' C).indicator (fun _ => (1 : ℝ)) | L] =ᵐ[P]
        P[(Y ⁻¹' C).indicator (fun _ => (1 : ℝ)) | H])
    {Z : Ω → ℝ} (hZ : StronglyMeasurable[L] Z) {c : ℝ} (hZ0 : ∀ ω, 0 ≤ Z ω)
    (hZc : ∀ ω, Z ω ≤ c) {g : Θ → ℝ} (hg : Measurable g) {c' : ℝ} (hgc : ∀ ρ, |g ρ| ≤ c') :
    ∫ ω, g (X ω) * Z ω ∂P = ∫ ω, (P[fun ω => g (Y ω) | H]) ω * Z ω ∂P := by
  have hZm : Measurable Z := hZ.measurable.mono hL le_rfl
  have hZa : ∀ ω, |Z ω| ≤ c := fun ω => by rw [abs_of_nonneg (hZ0 ω)]; exact hZc ω
  have hZi : Integrable Z P := Integrable.of_bound hZm.aestronglyMeasurable c
    (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hZa ω)
  set W := P[Z | H] with hW
  have hWm : Measurable W := (stronglyMeasurable_condExp.measurable).mono hH le_rfl
  have hW0 : 0 ≤ᵐ[P] W := condExp_nonneg (Filter.Eventually.of_forall hZ0)
  have hWi : Integrable W P := integrable_condExp
  have hind : ∀ {S : Set Ω}, MeasurableSet S → ∀ ω, |S.indicator (fun _ => (1 : ℝ)) ω| ≤ 1 :=
    fun {S} _ ω => by by_cases h : ω ∈ S <;> simp [h]
  -- step 1: indicators
  have step1 : ∀ C : Set Θ, MeasurableSet C →
      ∫ ω, (X ⁻¹' C).indicator (fun _ => (1 : ℝ)) ω * Z ω ∂P
        = ∫ ω, (Y ⁻¹' C).indicator (fun _ => (1 : ℝ)) ω * W ω ∂P := by
    intro C hC
    have hXC : MeasurableSet (X ⁻¹' C) := hX hC
    have hYC : MeasurableSet (Y ⁻¹' C) := hY hC
    have hfi : Integrable ((X ⁻¹' C).indicator (fun _ => (1 : ℝ))) P :=
      (integrable_const (1 : ℝ)).indicator hXC
    have hint : Integrable ((X ⁻¹' C).indicator (fun _ => (1 : ℝ)) * Z) P :=
      hfi.mul_bdd hZm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hZa ω)
    have e1 : ∫ ω, (X ⁻¹' C).indicator (fun _ => (1 : ℝ)) ω * Z ω ∂P
        = ∫ ω, (P[(X ⁻¹' C).indicator (fun _ => (1 : ℝ)) * Z | L]) ω ∂P :=
      (integral_condExp hL).symm
    rw [e1, integral_congr_ae (condExp_mul_of_stronglyMeasurable_right hZ hint hfi)]
    have h2 : ∫ ω, (P[(X ⁻¹' C).indicator (fun _ => (1 : ℝ)) | L] * Z) ω ∂P
        = ∫ ω, (P[(Y ⁻¹' C).indicator (fun _ => (1 : ℝ)) | H]) ω * Z ω ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [hs C hC] with ω hω
      simp [hω]
    rw [h2]
    exact condExp_selfadj hH ((measurable_const.indicator hYC)) hZm (hind hYC) hZa
  -- step 2: measures
  have hfin1 : IsFiniteMeasure (P.withDensity (fun ω => ENNReal.ofReal (Z ω))) :=
    isFiniteMeasure_withDensity_ofReal hZi.2
  have hfin2 : IsFiniteMeasure (P.withDensity (fun ω => ENNReal.ofReal (W ω))) :=
    isFiniteMeasure_withDensity_ofReal hWi.2
  have heq : (P.withDensity (fun ω => ENNReal.ofReal (Z ω))).map X
      = (P.withDensity (fun ω => ENNReal.ofReal (W ω))).map Y := by
    ext C hC
    rw [Measure.map_apply hX hC, Measure.map_apply hY hC,
      wd_apply hZi (Filter.Eventually.of_forall hZ0) (hX hC), wd_apply hWi hW0 (hY hC), step1 C hC]
  have hint_eq : ∀ (U : Ω → Θ) (hU : Measurable U) (V : Ω → ℝ) (hV : Measurable V)
      (hV0 : 0 ≤ᵐ[P] V),
      ∫ x, g x ∂((P.withDensity (fun ω => ENNReal.ofReal (V ω))).map U)
        = ∫ ω, g (U ω) * V ω ∂P := by
    intro U hU V hV hV0
    rw [integral_map hU.aemeasurable hg.aestronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul (f := fun ω => ENNReal.ofReal (V ω))
        (ENNReal.measurable_ofReal.comp hV)
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae ?_
    filter_upwards [hV0] with ω hω
    simp [ENNReal.toReal_ofReal hω, mul_comm]
  have hgi : ∀ ω, |g (Y ω)| ≤ c' := fun ω => hgc _
  rw [← hint_eq X hX Z hZm (Filter.Eventually.of_forall hZ0), heq, hint_eq Y hY W hWm hW0,
    condExp_selfadj (f := fun ω => g (Y ω)) hH (hg.comp hY) hZm hgi hZa]

theorem meanDemand_mem {N K : ℕ} {Θ : Type*} [MeasurableSpace Θ] {dbar : Fin N → ℝ}
    {F : Kernel (Θ × Fin K) (Fin N → ℝ)} [IsMarkovKernel F]
    (hF : ∀ ρ k, ∀ᵐ x ∂(F (ρ, k)), ∀ i, x i ∈ Set.Icc 0 (dbar i)) (ρ : Θ) (i : Fin N)
    (k : Fin K) : meanDemand F ρ i k ∈ Set.Icc 0 (dbar i) := by
  have hb : ∀ᵐ x ∂(F (ρ, k)), x i ∈ Set.Icc 0 (dbar i) := by
    filter_upwards [hF ρ k] with x hx using hx i
  have hint : Integrable (fun x : Fin N → ℝ => x i) (F (ρ, k)) :=
    Integrable.of_bound (measurable_pi_apply i).aestronglyMeasurable (|dbar i|) (by
      filter_upwards [hb] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg hx.1, abs_of_nonneg (hx.1.trans hx.2)]; exact hx.2)
  constructor
  · exact integral_nonneg_of_ae (by filter_upwards [hb] with x hx using hx.1)
  · have := integral_mono_ae hint (integrable_const (dbar i)) (by
      filter_upwards [hb] with x hx using hx.2)
    simpa [meanDemand] using this

theorem meanDemand_measurable {N K : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (F : Kernel (Θ × Fin K) (Fin N → ℝ)) (i : Fin N) (k : Fin K) :
    Measurable (fun ρ => meanDemand F ρ i k) := by
  have hg : Measurable (fun ρ : Θ => (ρ, k)) := measurable_id.prodMk measurable_const
  exact ((measurable_pi_apply i).stronglyMeasurable.integral_kernel
    (κ := F.comap (fun ρ : Θ => (ρ, k)) hg)).measurable

theorem reward_bounds {N K : ℕ} {Θ : Type*} [MeasurableSpace Θ] {dbar : Fin N → ℝ}
    {p : Fin N → Fin K → ℝ} (hp : ∀ i k, 0 ≤ p i k)
    {F : Kernel (Θ × Fin K) (Fin N → ℝ)} [IsMarkovKernel F]
    (hF : ∀ ρ k, ∀ᵐ x ∂(F (ρ, k)), ∀ i, x i ∈ Set.Icc 0 (dbar i)) (ρ : Θ) (k : Fin K) :
    0 ≤ ∑ i : Fin N, p i k * meanDemand F ρ i k ∧
      ∑ i : Fin N, p i k * meanDemand F ρ i k ≤ ∑ i : Fin N, p i k * dbar i :=
  ⟨Finset.sum_nonneg fun i _ => mul_nonneg (hp i k) (meanDemand_mem hF ρ i k).1,
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (meanDemand_mem hF ρ i k).2 (hp i k)⟩

theorem histSigma_le {Ω : Type*} [mΩ : MeasurableSpace Ω] {N K : ℕ}
    {A : ℕ → Ω → Option (Fin K)} {D : ℕ → Ω → Fin N → ℝ}
    (hA : ∀ s, Measurable (A s)) (hD : ∀ s, Measurable (D s)) (t : ℕ) :
    histSigma A D t ≤ mΩ :=
  iSup₂_le fun s _ => sup_le (hA s).comap_le (hD s).comap_le

theorem pastSigma_le {Ω Θ : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Θ] {N K : ℕ}
    {θ : Ω → Θ} {θs : ℕ → Ω → Θ}
    {A : ℕ → Ω → Option (Fin K)} {D : ℕ → Ω → Fin N → ℝ} (hθ : Measurable θ)
    (hθs : ∀ s, Measurable (θs s))
    (hA : ∀ s, Measurable (A s)) (hD : ∀ s, Measurable (D s)) (t : ℕ) :
    pastSigma θ θs A D t ≤ mΩ :=
  sup_le hθ.comap_le (iSup₂_le fun s _ =>
    sup_le (sup_le (hθs s).comap_le (hA s).comap_le) (hD s).comap_le)


theorem bigSigma_le {Ω Θ : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Θ] {N K : ℕ}
    {θ : Ω → Θ} {θs : ℕ → Ω → Θ}
    {A : ℕ → Ω → Option (Fin K)} {D : ℕ → Ω → Fin N → ℝ} (hθ : Measurable θ)
    (hθs : ∀ s, Measurable (θs s))
    (hA : ∀ s, Measurable (A s)) (hD : ∀ s, Measurable (D s)) (t : ℕ) :
    (pastSigma θ θs A D t ⊔ MeasurableSpace.comap (θs t) inferInstance ⊔
        MeasurableSpace.comap (A t) inferInstance) ≤ mΩ :=
  sup_le (sup_le (pastSigma_le hθ hθs hA hD t) (hθs t).comap_le) (hA t).comap_le

theorem key2
    {N K : ℕ} {dbar : Fin N → ℝ}
    {Θ : Type*} [MeasurableSpace Θ]
    {F : Kernel (Θ × Fin K) (Fin N → ℝ)} [IsMarkovKernel F]
    (hF : ∀ ρ k, ∀ᵐ x ∂(F (ρ, k)), ∀ i, x i ∈ Set.Icc 0 (dbar i))
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {θ : Ω → Θ} {θs : ℕ → Ω → Θ}
    {A : ℕ → Ω → Option (Fin K)} {D : ℕ → Ω → Fin N → ℝ} {t : ℕ}
    (hθ : Measurable θ) (hθs : ∀ s, Measurable (θs s))
    (hA : ∀ s, Measurable (A s)) (hD : ∀ s, Measurable (D s))
    (hdemand : ∀ B : Set (Fin N → ℝ), MeasurableSet B →
      condProb P (pastSigma θ θs A D t ⊔
          MeasurableSpace.comap (θs t) inferInstance ⊔
          MeasurableSpace.comap (A t) inferInstance) (D t ⁻¹' B) =ᵐ[P]
        fun ω => (demandLaw F (θ ω) (A t ω) B).toReal)
    (k : Fin K) {E : Set Ω} (hEm : MeasurableSet[(pastSigma θ θs A D t ⊔ MeasurableSpace.comap (θs t) inferInstance ⊔
        MeasurableSpace.comap (A t) inferInstance)] E)
    (hEk : E ⊆ A t ⁻¹' {some k}) {B : Set (Fin N → ℝ)} (hB : MeasurableSet B) :
    P (E ∩ D t ⁻¹' B) = ∫⁻ ω in E, F (θ ω, k) B ∂P := by
  have hm := bigSigma_le hθ hθs hA hD t
  have hE : MeasurableSet E := hm _ hEm
  have hS : MeasurableSet (D t ⁻¹' B) := hD t hB
  have hf : Integrable ((D t ⁻¹' B).indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const (1 : ℝ)).indicator hS
  have h1 := setIntegral_condExp hm hf hEm
  have h2 : ∫ ω in E, (P[(D t ⁻¹' B).indicator (fun _ => (1 : ℝ)) | (pastSigma θ θs A D t ⊔ MeasurableSpace.comap (θs t) inferInstance ⊔
        MeasurableSpace.comap (A t) inferInstance)]) ω ∂P
      = ∫ ω in E, (F (θ ω, k) B).toReal ∂P := by
    have hd := hdemand B hB
    unfold condProb at hd
    rw [integral_congr_ae (ae_restrict_of_ae hd)]
    refine setIntegral_congr_fun hE (fun ω hω => ?_)
    have := hEk hω
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at this
    simp [this, demandLaw]
  rw [h2, setIntegral_indicator hS, setIntegral_const, smul_eq_mul, mul_one,
    Measure.real] at h1
  have hmeas : Measurable (fun ω => F (θ ω, k) B) :=
    (F.measurable_coe hB).comp (hθ.prodMk measurable_const)
  rw [integral_toReal hmeas.aemeasurable (Filter.Eventually.of_forall fun _ => measure_lt_top _ _)]
    at h1
  rw [ENNReal.toReal_eq_toReal_iff'] at h1
  · exact h1.symm
  · exact (lintegral_mono fun ω => prob_le_one).trans_lt (by simp) |>.ne
  · exact measure_ne_top _ _

theorem Ek_meas {Ω Θ : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Θ] {N K : ℕ}
    {θ : Ω → Θ} {θs : ℕ → Ω → Θ}
    {A : ℕ → Ω → Option (Fin K)} {D : ℕ → Ω → Fin N → ℝ} {t : ℕ} (a : Option (Fin K)) :
    MeasurableSet[(pastSigma θ θs A D t ⊔ MeasurableSpace.comap (θs t) inferInstance ⊔
        MeasurableSpace.comap (A t) inferInstance)] (A t ⁻¹' {a}) :=
  le_sup_right (a := pastSigma θ θs A D t ⊔ MeasurableSpace.comap (θs t) inferInstance)
      _ ⟨{a}, trivial, rfl⟩

theorem demand_ae2
    {N K : ℕ} {dbar : Fin N → ℝ}
    {Θ : Type*} [MeasurableSpace Θ]
    {F : Kernel (Θ × Fin K) (Fin N → ℝ)} [IsMarkovKernel F]
    (hF : ∀ ρ k, ∀ᵐ x ∂(F (ρ, k)), ∀ i, x i ∈ Set.Icc 0 (dbar i))
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {θ : Ω → Θ} {θs : ℕ → Ω → Θ}
    {A : ℕ → Ω → Option (Fin K)} {D : ℕ → Ω → Fin N → ℝ} {t : ℕ}
    (hθ : Measurable θ) (hθs : ∀ s, Measurable (θs s))
    (hA : ∀ s, Measurable (A s)) (hD : ∀ s, Measurable (D s))
    (hdemand : ∀ B : Set (Fin N → ℝ), MeasurableSet B →
      condProb P (pastSigma θ θs A D t ⊔
          MeasurableSpace.comap (θs t) inferInstance ⊔
          MeasurableSpace.comap (A t) inferInstance) (D t ⁻¹' B) =ᵐ[P]
        fun ω => (demandLaw F (θ ω) (A t ω) B).toReal) :
    ∀ᵐ ω ∂P, A t ω = none ∨ ∀ i, D t ω i ∈ Set.Icc 0 (dbar i) := by
  set G : Set (Fin N → ℝ) := {x | ¬ ∀ i, x i ∈ Set.Icc 0 (dbar i)} with hG
  have hGm : MeasurableSet G := by
    have : G = (⋂ i, (fun x : Fin N → ℝ => x i) ⁻¹' Set.Icc 0 (dbar i))ᶜ := by
      ext x; simp [hG]
    rw [this]
    exact (MeasurableSet.iInter fun i => measurable_pi_apply i measurableSet_Icc).compl
  have hk : ∀ k : Fin K, ∀ᵐ ω ∂P, A t ω = some k → ∀ i, D t ω i ∈ Set.Icc 0 (dbar i) := by
    intro k
    have h0 : P (A t ⁻¹' {some k} ∩ D t ⁻¹' G) = 0 := by
      rw [key2 hF hθ hθs hA hD hdemand k (Ek_meas (some k)) le_rfl hGm]
      have : ∀ ω, F (θ ω, k) G = 0 := fun ω => ae_iff.mp (hF (θ ω) k)
      simp [this]
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with ω hω hA
    by_contra hc
    exact hω ⟨hA, hc⟩
  filter_upwards [ae_all_iff.mpr hk] with ω hω
  cases h : A t ω with
  | none => exact Or.inl rfl
  | some k => exact Or.inr (hω k h)

theorem coord2
    {N K : ℕ} {dbar : Fin N → ℝ}
    {Θ : Type*} [MeasurableSpace Θ]
    {F : Kernel (Θ × Fin K) (Fin N → ℝ)} [IsMarkovKernel F]
    (hF : ∀ ρ k, ∀ᵐ x ∂(F (ρ, k)), ∀ i, x i ∈ Set.Icc 0 (dbar i))
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {θ : Ω → Θ} {θs : ℕ → Ω → Θ}
    {A : ℕ → Ω → Option (Fin K)} {D : ℕ → Ω → Fin N → ℝ} {t : ℕ}
    (hθ : Measurable θ) (hθs : ∀ s, Measurable (θs s))
    (hA : ∀ s, Measurable (A s)) (hD : ∀ s, Measurable (D s))
    (hdemand : ∀ B : Set (Fin N → ℝ), MeasurableSet B →
      condProb P (pastSigma θ θs A D t ⊔
          MeasurableSpace.comap (θs t) inferInstance ⊔
          MeasurableSpace.comap (A t) inferInstance) (D t ⁻¹' B) =ᵐ[P]
        fun ω => (demandLaw F (θ ω) (A t ω) B).toReal)
    (k : Fin K) (i : Fin N) {E : Set Ω} (hEm : MeasurableSet[(pastSigma θ θs A D t ⊔ MeasurableSpace.comap (θs t) inferInstance ⊔
        MeasurableSpace.comap (A t) inferInstance)] E)
    (hEk : E ⊆ A t ⁻¹' {some k}) :
    (IntegrableOn (fun ω => D t ω i) E P ∧
      IntegrableOn (fun ω => meanDemand F (θ ω) i k) E P) ∧
    ∫ ω in E, D t ω i ∂P = ∫ ω in E, meanDemand F (θ ω) i k ∂P := by
  have hgm : Measurable (fun ω => (θ ω, k)) := hθ.prodMk measurable_const
  set κ : Kernel Ω (Fin N → ℝ) := F.comap (fun ω => (θ ω, k)) hgm with hκ
  have : IsMarkovKernel κ := by rw [hκ]; infer_instance
  have hE : MeasurableSet E := bigSigma_le hθ hθs hA hD t _ hEm
  have heq : (P.restrict E).map (D t) = κ ∘ₘ (P.restrict E) := by
    ext B hB
    rw [Measure.map_apply (hD t) hB, Measure.bind_apply hB κ.aemeasurable,
      Measure.restrict_apply (hD t hB), Set.inter_comm, key2 hF hθ hθs hA hD hdemand k hEm hEk hB]
    rfl
  have hbd : ∀ᵐ ω ∂(P.restrict E), ‖D t ω i‖ ≤ |dbar i| := by
    filter_upwards [ae_restrict_of_ae (demand_ae2 hF hθ hθs hA hD hdemand), ae_restrict_mem hE]
      with ω h hω
    have hω' := hEk hω
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hω'
    rcases h with h | h
    · rw [hω'] at h; cases h
    · have := h i
      rw [Real.norm_eq_abs, abs_of_nonneg this.1, abs_of_nonneg (this.1.trans this.2)]
      exact this.2
  have hint1 : IntegrableOn (fun ω => D t ω i) E P :=
    Integrable.of_bound ((measurable_pi_apply i).comp (hD t)).aestronglyMeasurable _ hbd
  have hint2 : Integrable (fun x : Fin N → ℝ => x i) ((P.restrict E).map (D t)) :=
    (integrable_map_measure (measurable_pi_apply i).aestronglyMeasurable
      (hD t).aemeasurable).mpr hint1
  have hmd : ∀ ω, meanDemand F (θ ω) i k = ∫ x, x i ∂(κ ω) := fun ω => rfl
  have hint3 : IntegrableOn (fun ω => meanDemand F (θ ω) i k) E P := by
    refine Integrable.of_bound
      ((meanDemand_measurable F i k).comp hθ).aestronglyMeasurable
      (|dbar i|) (Filter.Eventually.of_forall fun ω => ?_)
    have := meanDemand_mem hF (θ ω) i k
    rw [Real.norm_eq_abs, abs_of_nonneg this.1, abs_of_nonneg (this.1.trans this.2)]
    exact this.2
  refine ⟨⟨hint1, hint3⟩, ?_⟩
  rw [← integral_map (hD t).aemeasurable (measurable_pi_apply i).aestronglyMeasurable, heq]
  rw [heq] at hint2
  rw [Measure.comp_eq_comp_const_apply] at hint2 ⊢
  rw [ProbabilityTheory.Kernel.integral_comp hint2]
  simp [hmd]

theorem cond_transfer {Ω Θ : Type*} {H L : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace Θ] {P : Measure Ω}
    [IsProbabilityMeasure P] (hH : H ≤ mΩ) (hL : L ≤ mΩ) (hHL : H ≤ L)
    {X Y : Ω → Θ} (hX : Measurable X) (hY : Measurable Y)
    (hs : ∀ C : Set Θ, MeasurableSet C →
      P[(X ⁻¹' C).indicator (fun _ => (1 : ℝ)) | L] =ᵐ[P]
        P[(Y ⁻¹' C).indicator (fun _ => (1 : ℝ)) | H])
    {g : Θ → ℝ} (hg : Measurable g) {c' : ℝ} (hgc : ∀ ρ, |g ρ| ≤ c') :
    P[fun ω => g (Y ω) | H] =ᵐ[P] P[fun ω => g (X ω) | L] := by
  have hgX : Integrable (fun ω => g (X ω)) P :=
    Integrable.of_bound (hg.comp hX).aestronglyMeasurable c'
      (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hgc (X ω))
  refine ae_eq_condExp_of_forall_setIntegral_eq hL hgX
    (fun _ _ _ => integrable_condExp.integrableOn) (fun S hS _ => ?_)
    (stronglyMeasurable_condExp.mono hHL).aestronglyMeasurable
  have hSm : MeasurableSet S := hL _ hS
  have hZ : StronglyMeasurable[L] (S.indicator (fun _ => (1 : ℝ))) :=
    stronglyMeasurable_const.indicator hS
  have ht := transfer hH hL hX hY hs hZ (c := 1)
    (fun ω => by by_cases h : ω ∈ S <;> simp [h])
    (fun ω => by by_cases h : ω ∈ S <;> simp [h]) hg hgc
  have hconv : ∀ f : Ω → ℝ, ∫ ω, f ω * S.indicator (fun _ => (1 : ℝ)) ω ∂P = ∫ ω in S, f ω ∂P := by
    intro f
    rw [← integral_indicator hSm]
    congr 1; funext ω
    by_cases h : ω ∈ S <;> simp [h]
  rw [hconv, hconv] at ht
  exact ht.symm

end S216NRM


open MeasureTheory ProbabilityTheory OnlineNRM.TSFixed
open scoped BigOperators OnlineNRM.TSFixed
theorem solution
    {N K : ℕ} (hK : 1 ≤ K)
    (p : Fin N → Fin K → ℝ) (dbar : Fin N → ℝ)
    (hp : ∀ i k, 0 ≤ p i k)
    {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    (F : Kernel (Θ × Fin K) (Fin N → ℝ)) [IsMarkovKernel F]
    (hF : ∀ ρ k, ∀ᵐ x ∂(F (ρ, k)), ∀ i, x i ∈ Set.Icc 0 (dbar i))
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : Ω → Θ) (θs : ℕ → Ω → Θ)
    (A : ℕ → Ω → Option (Fin K)) (D : ℕ → Ω → Fin N → ℝ)
    (xsel : Θ → Fin K → ℝ) (t : ℕ)
    (hθ : Measurable θ) (hθs : ∀ s, Measurable (θs s))
    (hA : ∀ s, Measurable (A s)) (hD : ∀ s, Measurable (D s))
    (hx : Measurable xsel)
    (hx0 : ∀ ρ k, 0 ≤ xsel ρ k)
    (hx1 : ∀ ρ, ∑ k : Fin K, xsel ρ k ≤ 1)
    (hsample : ∀ C : Set Θ, MeasurableSet C →
      condProb P (pastSigma θ θs A D t) (θs t ⁻¹' C) =ᵐ[P]
        condProb P (histSigma A D t) (θ ⁻¹' C))
    (hoffer : ∀ k : Fin K,
      condProb P (pastSigma θ θs A D t ⊔
          MeasurableSpace.comap (θs t) inferInstance) (A t ⁻¹' {some k}) =ᵐ[P]
        fun ω => xsel (θs t ω) k)
    (hdemand : ∀ B : Set (Fin N → ℝ), MeasurableSet B →
      condProb P (pastSigma θ θs A D t ⊔
          MeasurableSpace.comap (θs t) inferInstance ⊔
          MeasurableSpace.comap (A t) inferInstance) (D t ⁻¹' B) =ᵐ[P]
        fun ω => (demandLaw F (θ ω) (A t ω) B).toReal) :
    IsFiniteOracleExperiment P (histSigma A D t) (pastSigma θ θs A D t)
      (histSigma A D (t + 1))
      (fun ω a => oracleActionWeights xsel (θ ω) a)
      (fun ω a => oracleMeanReward p F (θ ω) a)
      (A t) (observedPriceReward p (A t) (D t)) (pmax p dbar) := by
  have hH := S216NRM.histSigma_le hA hD t
  have hG := S216NRM.histSigma_le hA hD (t + 1)
  have hL := S216NRM.pastSigma_le hθ hθs hA hD t
  have hLL := S216NRM.bigSigma_le hθ hθs hA hD t
  have hL' : pastSigma θ θs A D t ⊔ MeasurableSpace.comap (θs t) inferInstance ≤ ‹MeasurableSpace Ω› :=
    sup_le hL (hθs t).comap_le
  have hLb : pastSigma θ θs A D t ⊔ MeasurableSpace.comap (A t) inferInstance ≤
      ‹MeasurableSpace Ω› := sup_le hL (hA t).comap_le
  have hLbLL : pastSigma θ θs A D t ⊔ MeasurableSpace.comap (A t) inferInstance ≤
      pastSigma θ θs A D t ⊔ MeasurableSpace.comap (θs t) inferInstance ⊔
        MeasurableSpace.comap (A t) inferInstance :=
    sup_le_sup_right le_sup_left _
  have hHL : histSigma A D t ≤ pastSigma θ θs A D t := by
    unfold histSigma pastSigma
    exact iSup₂_le fun s hs => le_sup_of_le_right (le_iSup₂_of_le s hs
      (sup_le_sup_right le_sup_right _))
  have hHG : histSigma A D t ≤ histSigma A D (t + 1) := by
    unfold histSigma
    exact iSup₂_le fun s hs => le_iSup₂_of_le (f := fun s (_ : s < t + 1) =>
      MeasurableSpace.comap (A s) inferInstance ⊔ MeasurableSpace.comap (D s) inferInstance)
      s (Nat.lt_succ_of_lt hs) le_rfl
  have hAtG : MeasurableSpace.comap (A t) inferInstance ⊔ MeasurableSpace.comap (D t) inferInstance
      ≤ histSigma A D (t + 1) := by
    unfold histSigma
    exact le_iSup₂_of_le (f := fun s (_ : s < t + 1) =>
      MeasurableSpace.comap (A s) inferInstance ⊔ MeasurableSpace.comap (D s) inferInstance)
      t (Nat.lt_succ_self t) le_rfl
  have hθL : Measurable[pastSigma θ θs A D t] θ :=
    (comap_measurable θ).mono le_sup_left le_rfl
  have hAG : Measurable[histSigma A D (t + 1)] (A t) :=
    (comap_measurable (A t)).mono (le_sup_left.trans hAtG) le_rfl
  have hDG : Measurable[histSigma A D (t + 1)] (D t) :=
    (comap_measurable (D t)).mono (le_sup_right.trans hAtG) le_rfl
  set r : Fin K → Θ → ℝ := fun k ρ => ∑ i : Fin N, p i k * meanDemand F ρ i k with hr
  have hrm : ∀ k, Measurable (r k) := fun k =>
    Finset.measurable_sum _ fun i _ => measurable_const.mul (S216NRM.meanDemand_measurable F i k)
  have hrb := S216NRM.reward_bounds hp hF
  have hxk : ∀ k, Measurable (fun ρ => xsel ρ k) := fun k => (measurable_pi_apply k).comp hx
  have hxb : ∀ ρ k, |xsel ρ k| ≤ 1 := fun ρ k => by
    rw [abs_of_nonneg (hx0 ρ k)]
    exact (Finset.single_le_sum (f := fun k => xsel ρ k) (fun k _ => hx0 ρ k)
      (Finset.mem_univ k)).trans (hx1 ρ)
  -- pmax facts
  have hne : (Finset.univ : Finset (Fin K)).Nonempty := ⟨⟨0, hK⟩, Finset.mem_univ _⟩
  have hle : ∀ k, ∑ i : Fin N, p i k * dbar i ≤ pmax p dbar := fun k => by
    unfold pmax; rw [dif_pos hne]
    exact Finset.le_sup' (fun k => ∑ i : Fin N, p i k * dbar i) (Finset.mem_univ k)
  have hdbar : ∀ i, 0 ≤ dbar i := by
    intro i
    obtain ⟨ω⟩ := nonempty_of_isProbabilityMeasure P
    obtain ⟨x, hx⟩ := (hF (θ ω) ⟨0, hK⟩).exists
    exact (hx i).1.trans (hx i).2
  have hpmax0 : 0 ≤ pmax p dbar :=
    (Finset.sum_nonneg fun i _ => mul_nonneg (hp i ⟨0, hK⟩) (hdbar i)).trans (hle ⟨0, hK⟩)
  -- reward decomposition
  have hEm : ∀ k : Fin K, MeasurableSet (A t ⁻¹' {some k}) := fun k =>
    hA t (MeasurableSet.singleton _)
  have hYdec : ∀ ω, observedPriceReward p (A t) (D t) ω = ∑ k : Fin K,
      (A t ⁻¹' {some k}).indicator (fun ω => ∑ i : Fin N, p i k * D t ω i) ω := by
    intro ω
    unfold observedPriceReward
    cases h : A t ω with
    | none => simp [h, postedPrice]
    | some k0 =>
      rw [Finset.sum_eq_single k0]
      · simp [h, postedPrice]
      · intro b _ hb; simp [h, Ne.symm hb]
      · simp
  have hgdec : ∀ ω, oracleMeanReward p F (θ ω) (A t ω) = ∑ k : Fin K,
      (A t ⁻¹' {some k}).indicator (fun ω => r k (θ ω)) ω := by
    intro ω
    cases h : A t ω with
    | none => simp [h, oracleMeanReward]
    | some k0 =>
      rw [Finset.sum_eq_single k0]
      · simp [h, oracleMeanReward, hr]
      · intro b _ hb; simp [h, Ne.symm hb]
      · simp
  have hYbd : ∀ᵐ ω ∂P, observedPriceReward p (A t) (D t) ω ∈ Set.Icc 0 (pmax p dbar) := by
    filter_upwards [S216NRM.demand_ae2 hF hθ hθs hA hD hdemand] with ω hω
    unfold observedPriceReward
    cases h : A t ω with
    | none => simp [postedPrice, hpmax0]
    | some k =>
      rcases hω with h' | h'
      · rw [h] at h'; cases h'
      simp only [postedPrice]
      refine ⟨Finset.sum_nonneg fun i _ => mul_nonneg (hp i k) (h' i).1, ?_⟩
      exact (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h' i).2 (hp i k)).trans
        (hle k)
  have hYm : Measurable (observedPriceReward p (A t) (D t)) := by
    unfold observedPriceReward
    exact Finset.measurable_sum _ fun i _ =>
      ((measurable_from_top (f := fun o : Option (Fin K) => postedPrice p o i)).comp (hA t)).mul
        ((measurable_pi_apply i).comp (hD t))
  have hYi : Integrable (observedPriceReward p (A t) (D t)) P :=
    Integrable.of_bound hYm.aestronglyMeasurable (pmax p dbar) (by
      filter_upwards [hYbd] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg hω.1]; exact hω.2)
  -- action law for some k
  have hsome : ∀ k : Fin K,
      P[(A t ⁻¹' {some k}).indicator (fun _ => (1 : ℝ)) | pastSigma θ θs A D t] =ᵐ[P]
        P[fun ω => xsel (θ ω) k | histSigma A D t] := by
    intro k
    have h1 := (condExp_condExp_of_le (μ := P)
      (f := (A t ⁻¹' {some k}).indicator (fun _ => (1 : ℝ))) le_sup_left hL').symm
    have h2 : P[P[(A t ⁻¹' {some k}).indicator (fun _ => (1 : ℝ)) |
        pastSigma θ θs A D t ⊔ MeasurableSpace.comap (θs t) inferInstance] |
          pastSigma θ θs A D t] =ᵐ[P] P[fun ω => xsel (θs t ω) k | pastSigma θ θs A D t] :=
      condExp_congr_ae (hoffer k)
    have h3 := S216NRM.cond_transfer hH hL hHL (hθs t) hθ hsample (hxk k) (fun ρ => hxb ρ k)
    exact h1.trans (h2.trans h3.symm)
  exact {
    history_le_latent := hHL
    latent_le_ambient := hL
    history_le_observed := hHG
    observed_le_ambient := hG
    measurable_weights := by
      letI : MeasurableSpace Ω := pastSigma θ θs A D t
      refine measurable_pi_lambda _ fun a => ?_
      cases a with
      | none =>
        exact measurable_const.sub (Finset.measurable_sum _ fun k _ => (hxk k).comp hθL)
      | some k => exact (hxk k).comp hθL
    measurable_means := by
      letI : MeasurableSpace Ω := pastSigma θ θs A D t
      refine measurable_pi_lambda _ fun a => ?_
      cases a with
      | none => exact measurable_const
      | some k => exact (hrm k).comp hθL
    measurable_action := hAG
    measurable_reward := by
      unfold observedPriceReward
      exact Finset.measurable_sum _ fun i _ =>
        ((measurable_from_top (f := fun o : Option (Fin K) => postedPrice p o i)).comp hAG).mul
          ((measurable_pi_apply i).comp hDG)
    weights_nonneg := by
      intro ω a
      cases a with
      | none => simp only [oracleActionWeights]; linarith [hx1 (θ ω)]
      | some k => exact hx0 _ k
    weights_sum := by
      intro ω
      rw [Fintype.sum_option]
      simp [oracleActionWeights]
    scale_nonneg := hpmax0
    means_bounded := Filter.Eventually.of_forall fun ω a => by
      cases a with
      | none => exact ⟨le_rfl, hpmax0⟩
      | some k => exact ⟨(hrb (θ ω) k).1, (hrb (θ ω) k).2.trans (hle k)⟩
    reward_bounded := hYbd
    action_law := by
      intro a
      cases a with
      | some k => exact hsome k
      | none =>
        have hind : (A t ⁻¹' {none}).indicator (fun _ => (1 : ℝ)) =
            (fun _ => (1 : ℝ)) - ∑ k : Fin K, (A t ⁻¹' {some k}).indicator (fun _ => (1 : ℝ)) := by
          funext ω
          cases h : A t ω with
          | none => simp [h]
          | some k0 =>
            simp only [Pi.sub_apply, Finset.sum_apply]
            rw [Finset.sum_eq_single k0]
            · simp [h]
            · intro b _ hb; simp [h, Ne.symm hb]
            · simp
        have hw : (fun ω => oracleActionWeights xsel (θ ω) none) =
            (fun _ => (1 : ℝ)) - ∑ k : Fin K, (fun ω => xsel (θ ω) k) := by
          funext ω; simp [oracleActionWeights]
        have hii : ∀ k ∈ (Finset.univ : Finset (Fin K)),
            Integrable ((A t ⁻¹' {some k}).indicator (fun _ => (1 : ℝ))) P :=
          fun k _ => (integrable_const (1 : ℝ)).indicator (hEm k)
        have hxi : ∀ k ∈ (Finset.univ : Finset (Fin K)),
            Integrable (fun ω => xsel (θ ω) k) P := fun k _ =>
          Integrable.of_bound ((hxk k).comp hθ).aestronglyMeasurable 1
            (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hxb (θ ω) k)
        rw [hind, hw]
        have e1 := condExp_sub (m := pastSigma θ θs A D t) (integrable_const (1 : ℝ))
          (integrable_finsetSum' _ hii)
        have e2 := condExp_finsetSum hii (pastSigma θ θs A D t)
        have e3 := condExp_sub (m := histSigma A D t) (integrable_const (1 : ℝ))
          (integrable_finsetSum' _ hxi)
        have e4 := condExp_finsetSum hxi (histSigma A D t)
        rw [condExp_const hL] at e1
        rw [condExp_const hH] at e3
        filter_upwards [e1, e2, e3, e4, ae_all_iff.mpr hsome] with ω h1 h2 h3 h4 h5
        rw [h1, h3]
        simp only [Pi.sub_apply]
        rw [h2, h4]
        simp only [Finset.sum_apply]
        rw [Finset.sum_congr rfl fun k _ => h5 k]
    reward_mean := by
      refine (ae_eq_condExp_of_forall_setIntegral_eq hLb hYi
        (fun S _ _ => ?_) (fun S hS _ => ?_) ?_).symm
      · rw [show (fun ω => oracleMeanReward p F (θ ω) (A t ω)) = (fun ω => ∑ k : Fin K,
            (A t ⁻¹' {some k}).indicator (fun ω => r k (θ ω)) ω) from funext hgdec]
        exact (Integrable.of_bound
          (Finset.measurable_sum _ fun k _ => Measurable.indicator (f := fun ω => r k (θ ω))
            ((hrm k).comp hθ) (hEm k)).aestronglyMeasurable
          (∑ k : Fin K, ∑ i : Fin N, p i k * dbar i)
          (Filter.Eventually.of_forall fun ω => by
            rw [Real.norm_eq_abs]
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
            by_cases h : ω ∈ A t ⁻¹' {some k}
            · rw [Set.indicator_of_mem h, abs_of_nonneg (hrb (θ ω) k).1]; exact (hrb (θ ω) k).2
            · rw [Set.indicator_of_notMem h, abs_zero]
              exact Finset.sum_nonneg fun i _ => mul_nonneg (hp i k) (hdbar i))).integrableOn
      · have hSL := hLbLL _ hS
        have hc := fun k i => S216NRM.coord2 hF hθ hθs hA hD hdemand k i
          (hSL.inter (S216NRM.Ek_meas (some k))) Set.inter_subset_right
        have hc0 := fun k i => S216NRM.coord2 hF hθ hθs hA hD hdemand k i
          (S216NRM.Ek_meas (some k)) le_rfl
        simp_rw [hgdec, hYdec]
        rw [integral_finsetSum _ fun k _ => (IntegrableOn.integrable_indicator
            (integrable_finsetSum _ fun i _ => ((hc0 k i).1.2.const_mul (p i k))) (hEm k)).restrict,
          integral_finsetSum _ fun k _ => (IntegrableOn.integrable_indicator
            (integrable_finsetSum _ fun i _ => ((hc0 k i).1.1.const_mul (p i k))) (hEm k)).restrict]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [setIntegral_indicator (hEm k), setIntegral_indicator (hEm k),
          integral_finsetSum _ fun i _ => (hc k i).1.2.const_mul (p i k),
          integral_finsetSum _ fun i _ => (hc k i).1.1.const_mul (p i k)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_const_mul, integral_const_mul, (hc k i).2]
      · have hθLb : Measurable[pastSigma θ θs A D t ⊔ MeasurableSpace.comap (A t) inferInstance] θ :=
          hθL.mono le_sup_left le_rfl
        have hEb : ∀ k : Fin K, MeasurableSet[pastSigma θ θs A D t ⊔
            MeasurableSpace.comap (A t) inferInstance] (A t ⁻¹' {some k}) := fun k =>
          le_sup_right (a := pastSigma θ θs A D t) _ ⟨{some k}, trivial, rfl⟩
        have : Measurable[pastSigma θ θs A D t ⊔ MeasurableSpace.comap (A t) inferInstance]
            (fun ω => ∑ k : Fin K, (A t ⁻¹' {some k}).indicator (fun ω => r k (θ ω)) ω) :=
          Finset.measurable_sum _ fun k _ => ((hrm k).comp hθLb).indicator (hEb k)
        have heq : (fun ω => oracleMeanReward p F (θ ω) (A t ω)) =
            (fun ω => ∑ k : Fin K, (A t ⁻¹' {some k}).indicator (fun ω => r k (θ ω)) ω) :=
          funext hgdec
        rw [heq]
        exact this.stronglyMeasurable.aestronglyMeasurable }
