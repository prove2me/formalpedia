-- Prove2me | solution 1 for OnlineNRM.TSFixed.posterior_matching_gap_covariance_identity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:30:51.467191+00:00
-- url     : https://prove2.me/submissions/cef88002-b718-4bc6-a7a2-38402ea50835

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

end S216NRM

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
        condProb P (histSigma A D t) (θ ⁻¹' C)) :
    (∫ ω, lpObj p (meanDemand F (θ ω)) (xsel (θ ω)) -
      lpObj p (meanDemand F (θ ω)) (xsel (θs t ω)) ∂P) =
      ∑ a : Option (Fin K), weightedOracleCovariance P (histSigma A D t)
        (fun ω b => oracleActionWeights xsel (θ ω) b)
        (fun ω b => oracleMeanReward p F (θ ω) b) a := by
  have hH := S216NRM.histSigma_le hA hD t
  have hL := S216NRM.pastSigma_le hθ hθs hA hD t
  set r : Fin K → Θ → ℝ := fun k ρ => ∑ i : Fin N, p i k * meanDemand F ρ i k with hr
  have hrm : ∀ k, Measurable (r k) := fun k =>
    Finset.measurable_sum _ fun i _ => measurable_const.mul (S216NRM.meanDemand_measurable F i k)
  have hrb := S216NRM.reward_bounds hp hF
  have hxk : ∀ k, Measurable (fun ρ => xsel ρ k) := fun k => (measurable_pi_apply k).comp hx
  have hxb : ∀ ρ k, |xsel ρ k| ≤ 1 := fun ρ k => by
    rw [abs_of_nonneg (hx0 ρ k)]
    exact (Finset.single_le_sum (f := fun k => xsel ρ k) (fun k _ => hx0 ρ k)
      (Finset.mem_univ k)).trans (hx1 ρ)
  have hrabs : ∀ k ρ, |r k ρ| ≤ ∑ i : Fin N, p i k * dbar i := fun k ρ => by
    rw [abs_of_nonneg (hrb ρ k).1]; exact (hrb ρ k).2
  have hbint : ∀ (f : Ω → ℝ) (c : ℝ), Measurable f → (∀ ω, |f ω| ≤ c) → Integrable f P :=
    fun f c hf hc => Integrable.of_bound hf.aestronglyMeasurable c
      (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hc ω)
  have hprod : ∀ (ψ : Ω → Θ), Measurable ψ → ∀ k,
      Integrable (fun ω => r k (θ ω) * xsel (ψ ω) k) P := by
    intro ψ hψ k
    refine hbint _ ((∑ i : Fin N, p i k * dbar i) * 1) (((hrm k).comp hθ).mul ((hxk k).comp hψ)) ?_
    intro ω
    rw [abs_mul]
    exact mul_le_mul (hrabs k _) (hxb _ k) (abs_nonneg _) ((abs_nonneg _).trans (hrabs k (θ ω)))
  have htr : ∀ k, ∫ ω, xsel (θs t ω) k * r k (θ ω) ∂P
      = ∫ ω, (P[fun ω => xsel (θ ω) k | histSigma A D t]) ω * r k (θ ω) ∂P := by
    intro k
    have hZ : StronglyMeasurable[pastSigma θ θs A D t] (fun ω => r k (θ ω)) := by
      have h1 : Measurable[MeasurableSpace.comap θ inferInstance] (fun ω => r k (θ ω)) :=
        (hrm k).comp (comap_measurable θ)
      exact h1.stronglyMeasurable.mono le_sup_left
    exact S216NRM.transfer hH hL (hθs t) hθ hsample hZ (fun ω => (hrb (θ ω) k).1)
      (fun ω => (hrb (θ ω) k).2) (hxk k) (fun ρ => hxb ρ k)
  rw [Fintype.sum_option]
  simp only [weightedOracleCovariance, oracleMeanReward, oracleActionWeights, mul_zero,
    integral_zero, zero_add]
  have hrdef : ∀ k ρ, ∑ i : Fin N, p i k * meanDemand F ρ i k = r k ρ := fun _ _ => rfl
  simp only [hrdef]
  have hL1 : ∀ ω, lpObj p (meanDemand F (θ ω)) (xsel (θ ω)) -
      lpObj p (meanDemand F (θ ω)) (xsel (θs t ω)) =
      ∑ k : Fin K, (r k (θ ω) * xsel (θ ω) k - r k (θ ω) * xsel (θs t ω) k) := by
    intro ω; simp only [lpObj, hr, Finset.sum_sub_distrib]
  simp_rw [hL1]
  rw [integral_finsetSum (f := fun k ω => r k (θ ω) * xsel (θ ω) k - r k (θ ω) * xsel (θs t ω) k)
    _ fun k _ => (hprod θ hθ k).sub (hprod (θs t) (hθs t) k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hci : Integrable (fun ω => (P[fun ω => xsel (θ ω) k | histSigma A D t]) ω * r k (θ ω)) P :=
    integrable_condExp.mul_bdd ((hrm k).comp hθ).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        simpa [Real.norm_eq_abs] using hrabs k (θ ω))
  simp_rw [sub_mul]
  rw [integral_sub (hprod θ hθ k) (hprod (θs t) (hθs t) k), integral_sub _ hci]
  · congr 1
    · congr 1; funext ω; ring
    · rw [← htr k]; congr 1; funext ω; ring
  · simpa [mul_comm] using hprod θ hθ k
