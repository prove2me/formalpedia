-- Prove2me | solution 1 for PowerFIPP.Charact.lemma_3_2_ii
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T10:30:49.722382+00:00
-- url     : https://prove2.me/submissions/ed5f3812-5d9f-42d4-8ab5-f3dfa43f8e01
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PowerFIPP_Charact_Model
import Theorems.Thm_PowerFIPP_Charact_lemma_3_1
import Theorems.Thm_PowerFIPP_Charact_lemma_3_2_i

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped NNReal ENNReal

open PowerFIPP.Charact

namespace PFIPPAux

/-- Completeness: a function a.e. equal to an `mt`-measurable one is `mt`-measurable when every
`P`-null set is `mt`-measurable. -/
theorem sm_of_ae {Ω : Type*} {mt : MeasurableSpace Ω} [m : MeasurableSpace Ω] {P : Measure Ω}
    (hnull : ∀ A : Set Ω, P A = 0 → MeasurableSet[mt] A) {f g : Ω → ℝ}
    (hg : StronglyMeasurable[mt] g) (hfg : f =ᵐ[P] g) : StronglyMeasurable[mt] f := by
  have hN : P {ω | ¬ f ω = g ω} = 0 := ae_iff.1 hfg
  have hm : Measurable[mt] f := by
    intro B hB
    have h1 : MeasurableSet[mt] (g ⁻¹' B \ {ω | ¬ f ω = g ω}) :=
      (hg.measurable hB).diff (hnull _ hN)
    have h2 : MeasurableSet[mt] (f ⁻¹' B ∩ {ω | ¬ f ω = g ω}) :=
      hnull _ (measure_mono_null Set.inter_subset_right hN)
    have : f ⁻¹' B = (g ⁻¹' B \ {ω | ¬ f ω = g ω}) ∪ (f ⁻¹' B ∩ {ω | ¬ f ω = g ω}) := by
      ext ω
      by_cases h : f ω = g ω <;> simp [h]
    rw [this]
    exact h1.union h2
  exact hm.stronglyMeasurable

/-- Change of measure on a sub-σ-algebra: if `Q = G · P` on `mt`, then for `mt`-measurable `f`,
`f ∈ L¹(Q) ↔ G f ∈ L¹(P)` and `E^Q f = E^P[G f]`. -/
theorem com {Ω : Type*} {mt : MeasurableSpace Ω} [m : MeasurableSpace Ω] (hle : mt ≤ m)
    (P Q : Measure Ω) (g : Ω → ℝ) (hg : StronglyMeasurable[mt] g) (hgpos : ∀ ω, 0 ≤ g ω)
    (hdens : ∀ A, MeasurableSet[mt] A → Q A = ∫⁻ ω in A, ENNReal.ofReal (g ω) ∂P)
    (f : Ω → ℝ) (hf : StronglyMeasurable[mt] f) :
    (Integrable f Q ↔ Integrable (fun ω => g ω * f ω) P) ∧
      ∫ ω, f ω ∂Q = ∫ ω, g ω * f ω ∂P := by
  have hgm : Measurable[mt] (fun ω => (g ω).toNNReal) := hg.measurable.real_toNNReal
  have htrim : Q.trim hle = (P.trim hle).withDensity (fun ω => ((g ω).toNNReal : ℝ≥0∞)) := by
    refine @Measure.ext Ω mt _ _ fun A hA => ?_
    rw [trim_measurableSet_eq hle hA, withDensity_apply _ hA, hdens A hA]
    exact (setLIntegral_trim hle hgm.coe_nnreal_ennreal hA).symm
  have hfun : (fun ω => (g ω).toNNReal • f ω) = fun ω => g ω * f ω := by
    funext ω
    rw [NNReal.smul_def, Real.coe_toNNReal _ (hgpos ω), smul_eq_mul]
  have hgf : StronglyMeasurable[mt] (fun ω => g ω * f ω) := hg.mul hf
  refine ⟨⟨fun hQ => ?_, fun hP => ?_⟩, ?_⟩
  · have h1 := hQ.trim hle hf
    rw [htrim, integrable_withDensity_iff_integrable_smul hgm, hfun] at h1
    exact integrable_of_integrable_trim hle h1
  · have h1 := hP.trim hle hgf
    rw [← hfun, ← integrable_withDensity_iff_integrable_smul hgm, ← htrim] at h1
    exact integrable_of_integrable_trim hle h1
  · have e : ∫ ω, f ω ∂((P.trim hle).withDensity fun ω => ((g ω).toNNReal : ℝ≥0∞)) =
        ∫ ω, (g ω).toNNReal • f ω ∂(P.trim hle) := by
      let _ := mt
      exact integral_withDensity_eq_integral_smul hgm f
    rw [integral_trim hle hf, htrim, e, hfun, ← integral_trim hle hgf]

/-- Transfer of the supermartingale property through equal set integrals. -/
theorem super_transfer {Ω : Type*} [m : MeasurableSpace Ω] {ℱ : Filtration ℝ≥0 m}
    {μ ν : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure ν] {X Y : ℝ≥0 → Ω → ℝ}
    (hY : StronglyAdapted ℱ Y) (hint : ∀ t, Integrable (X t) μ → Integrable (Y t) ν)
    (hset : ∀ s t, s ≤ t → ∀ A, MeasurableSet[ℱ s] A →
      ∫ ω in A, X t ω ∂μ = ∫ ω in A, Y t ω ∂ν)
    (hX : Supermartingale X ℱ μ) : Supermartingale Y ℱ ν := by
  rw [← neg_neg Y]
  refine (submartingale_of_setIntegral_le hY.neg
    (fun i => (hint i (hX.integrable i)).neg) ?_).neg
  intro i j hij s hs
  simp only [Pi.neg_apply, integral_neg, neg_le_neg_iff]
  rw [← hset i j hij s hs, ← hset i i le_rfl s hs]
  exact hX.setIntegral_le hij hs

/-- Transfer of the martingale property through equal set integrals. -/
theorem mart_transfer {Ω : Type*} [m : MeasurableSpace Ω] {ℱ : Filtration ℝ≥0 m}
    {μ ν : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure ν] {X Y : ℝ≥0 → Ω → ℝ}
    (hY : StronglyAdapted ℱ Y) (hint : ∀ t, Integrable (X t) μ → Integrable (Y t) ν)
    (hset : ∀ s t, s ≤ t → ∀ A, MeasurableSet[ℱ s] A →
      ∫ ω in A, X t ω ∂μ = ∫ ω in A, Y t ω ∂ν)
    (hX : Martingale X ℱ μ) : Martingale Y ℱ ν := by
  have h1 := super_transfer hY hint hset hX.supermartingale
  have h2 : Supermartingale (-Y) ℱ ν := by
    refine super_transfer (X := -X) hY.neg (fun t h => ?_) (fun s t hst A hA => ?_)
      hX.neg.supermartingale
    · have h' : Integrable (X t) μ := by simpa using h.neg
      simpa using (hint t h').neg
    · simp only [Pi.neg_apply, integral_neg, hset s t hst A hA]
  have h3 : Submartingale Y ℱ ν := by simpa using h2.neg
  exact martingale_iff.2 ⟨h1, h3⟩

/-- **Bayes' rule for (super)martingales.** Let `Q = G_t · P` on `𝓕_t` for every `t`, with
`G > 0` adapted and the filtration complete for `P`. If `X_t = G_t Y_t` `P`-a.s. for each `t`,
then `X` is a `P`-supermartingale (martingale) iff `Y` is a `Q`-supermartingale (martingale). -/
theorem bayes {Ω : Type*} [m : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 m) (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hnull : ∀ A : Set Ω, P A = 0 → MeasurableSet[ℱ 0] A)
    (G : ℝ≥0 → Ω → ℝ) (hGm : ∀ t, StronglyMeasurable[ℱ t] (G t)) (hGpos : ∀ t ω, 0 < G t ω)
    (hdens : ∀ t A, MeasurableSet[ℱ t] A → Q A = ∫⁻ ω in A, ENNReal.ofReal (G t ω) ∂P)
    (X Y : ℝ≥0 → Ω → ℝ) (hXY : ∀ t, X t =ᵐ[P] fun ω => G t ω * Y t ω) :
    (Supermartingale X ℱ P ↔ Supermartingale Y ℱ Q) ∧
      (Martingale X ℱ P ↔ Martingale Y ℱ Q) := by
  have hnt : ∀ t (A : Set Ω), P A = 0 → MeasurableSet[ℱ t] A :=
    fun t A h => ℱ.mono (zero_le : (0 : ℝ≥0) ≤ t) _ (hnull A h)
  have adXY : StronglyAdapted ℱ X → StronglyAdapted ℱ Y := by
    intro hX t
    have hae : Y t =ᵐ[P] fun ω => X t ω / G t ω := by
      filter_upwards [hXY t] with ω h
      rw [h]
      field_simp [(hGpos t ω).ne']
    exact sm_of_ae (g := fun ω => X t ω / G t ω) (hnt t)
      (((hX t).measurable.div (hGm t).measurable).stronglyMeasurable) hae
  have adYX : StronglyAdapted ℱ Y → StronglyAdapted ℱ X := fun hY t =>
    sm_of_ae (g := fun ω => G t ω * Y t ω) (hnt t) ((hGm t).mul (hY t)) (hXY t)
  have core : StronglyAdapted ℱ Y → ∀ t, (Integrable (X t) P ↔ Integrable (Y t) Q) ∧
      ∀ s, s ≤ t → ∀ A, MeasurableSet[ℱ s] A →
        ∫ ω in A, X t ω ∂P = ∫ ω in A, Y t ω ∂Q := by
    intro hY t
    refine ⟨?_, fun s hst A hA => ?_⟩
    · rw [(com (ℱ.le t) P Q (G t) (hGm t) (fun ω => (hGpos t ω).le) (hdens t) (Y t)
        (hY t)).1]
      exact integrable_congr (hXY t)
    · have hAt : MeasurableSet[ℱ t] A := ℱ.mono hst _ hA
      have hc := (com (ℱ.le t) P Q (G t) (hGm t) (fun ω => (hGpos t ω).le) (hdens t)
        (A.indicator (Y t)) ((hY t).indicator hAt)).2
      rw [integral_indicator (ℱ.le t _ hAt)] at hc
      rw [hc]
      have : (fun ω => G t ω * A.indicator (Y t) ω) = A.indicator (fun ω => G t ω * Y t ω) := by
        funext ω
        by_cases h : ω ∈ A <;> simp [h]
      rw [this, integral_indicator (ℱ.le t _ hAt)]
      exact integral_congr_ae (ae_restrict_of_ae (hXY t))
  refine ⟨⟨fun hX => ?_, fun hY' => ?_⟩, ⟨fun hX => ?_, fun hY' => ?_⟩⟩
  · have hY := adXY hX.1
    exact super_transfer hY (fun t => (core hY t).1.1) (fun s t hst A hA => (core hY t).2 s hst A hA)
      hX
  · have hY := hY'.1
    exact super_transfer (adYX hY) (fun t => (core hY t).1.2)
      (fun s t hst A hA => ((core hY t).2 s hst A hA).symm) hY'
  · have hY := adXY hX.1
    exact mart_transfer hY (fun t => (core hY t).1.1) (fun s t hst A hA => (core hY t).2 s hst A hA)
      hX
  · have hY := hY'.1
    exact mart_transfer (adYX hY) (fun t => (core hY t).1.2)
      (fun s t hst A hA => ((core hY t).2 s hst A hA).symm) hY'

/-- For a continuous finite-variation path the Doléans-Dade exponential is `exp(V_t - V_0)`. -/
theorem stochExp_of_continuous {Ω : Type*} (Vf : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (hc : Continuous fun t => Vf t ω) (t : ℝ≥0) :
    stochExp Vf (fun _ _ => 0) t ω = Real.exp (Vf t ω - Vf 0 ω) := by
  have hj : ∀ s, jump Vf s ω = 0 := by
    intro s
    simp only [jump, PowerFIPP.Charact.leftLim]
    rcases Filter.eq_or_neBot (𝓝[<] s) with h | h
    · rw [leftLim_eq_of_eq_bot _ h, sub_self]
    · rw [leftLim_eq_of_tendsto ((hc.tendsto s).mono_left nhdsWithin_le_nhds), sub_self]
  simp [stochExp, hj]

/-- `x ↦ c x^p / p` is concave and increasing on `(0, ∞)` for `c ≥ 0`, `p < 1`, `p ≠ 0`. -/
theorem pow_div_concave (c p : ℝ) (hc : 0 ≤ c) (hp0 : p ≠ 0) (hp1 : p < 1) :
    ConcaveOn ℝ (Set.Ioi 0) (fun x : ℝ => c * x ^ p / p) ∧
      MonotoneOn (fun x : ℝ => c * x ^ p / p) (Set.Ioi 0) := by
  rcases lt_or_gt_of_ne hp0 with hp | hp
  · have hconv : ConvexOn ℝ (Set.Ioi 0) (fun x : ℝ => x ^ p) := by
      refine ⟨convex_Ioi 0, fun x hx y hy a b ha hb hab => ?_⟩
      have hx' : 0 < x := hx
      have hy' : 0 < y := hy
      have hxy : 0 < a * x + b * y := by
        rcases eq_or_lt_of_le ha with h | h
        · subst h
          have hb1 : b = 1 := by linarith
          subst hb1
          simpa using hy'
        · exact add_pos_of_pos_of_nonneg (mul_pos h hx') (mul_nonneg hb hy'.le)
      have hlog := strictConcaveOn_log_Ioi.concaveOn.2 hx hy ha hb hab
      simp only [smul_eq_mul] at hlog ⊢
      rw [Real.rpow_def_of_pos hxy, Real.rpow_def_of_pos hx', Real.rpow_def_of_pos hy']
      calc Real.exp (Real.log (a * x + b * y) * p)
          ≤ Real.exp (a * (Real.log x * p) + b * (Real.log y * p)) := by
            apply Real.exp_le_exp.2
            nlinarith [mul_le_mul_of_nonpos_left hlog hp.le]
        _ ≤ a * Real.exp (Real.log x * p) + b * Real.exp (Real.log y * p) := by
            have := convexOn_exp.2 (Set.mem_univ (Real.log x * p))
              (Set.mem_univ (Real.log y * p)) ha hb hab
            simpa [smul_eq_mul] using this
    have hc' : 0 ≤ c / -p := div_nonneg hc (neg_nonneg.2 hp.le)
    have e : ∀ z : ℝ, c * z ^ p / p = -(c / -p * z ^ p) := fun z => by
      field_simp
    have h1 : ConcaveOn ℝ (Set.Ioi 0) (fun x : ℝ => -((c / -p) • x ^ p)) :=
      (hconv.smul hc').neg
    refine ⟨h1.congr fun x _ => ?_, fun x hx y hy hxy => ?_⟩
    · simp only [smul_eq_mul, e]
    · have := Real.rpow_le_rpow_of_nonpos hx hxy hp.le
      simp only [e]
      nlinarith [mul_le_mul_of_nonneg_left this hc']
  · have h0 := (Real.concaveOn_rpow hp.le hp1.le).subset Set.Ioi_subset_Ici_self (convex_Ioi 0)
    have h1 := h0.smul (div_nonneg hc hp.le)
    have e : ∀ z : ℝ, c * z ^ p / p = c / p * z ^ p := fun z => by ring
    refine ⟨h1.congr fun x _ => ?_, fun x hx y hy hxy => ?_⟩
    · simp only [smul_eq_mul, e]
    · have := Real.rpow_le_rpow (le_of_lt hx) hxy hp.le
      simp only [e]
      exact mul_le_mul_of_nonneg_left this (div_nonneg hc hp.le)

end PFIPPAux

open PFIPPAux

theorem solution {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (mkt : Market Ω n) (p : ℝ)
    (hS : mkt.Standing P ℱ) (hp0 : p ≠ 0) (hp1 : p < 1) (hAD : AD P mkt)
    (M Dc J : ℝ≥0 → Ω → ℝ) (hM : IsLemma31MV P ℱ mkt M Dc J)
    (Q : Measure Ω) (hQ : IsQM P ℱ mkt M Q) (πstar : ℝ≥0 → Ω → Fin n → ℝ) :
    IsFIPP P P ℱ mkt (U mkt p) πstar ↔ IsFIPP Q P ℱ mkt (UV mkt p) πstar := by
  -- Lemma 3.2 (i)
  have hG := lemma_3_2_i P ℱ mkt p hS hp0 hp1 hAD M Dc J hM Q hQ
  -- Lemma 3.1: `e^D = e^{D_0} 𝓔(M) 𝓔(V)`, `V` adapted and continuous
  obtain ⟨hid, -, hVad, hVc, -⟩ := (lemma_3_1 P ℱ mkt hS hAD).2 M Dc J hM
  obtain ⟨hPprob, -, hnull, -, -, -, hDchar, -⟩ := hS
  obtain ⟨hQprob, hQP, -, hdensEM⟩ := hQ
  -- `D` is adapted
  have hDad : ∀ t, StronglyMeasurable[ℱ t] (mkt.D t) := by
    intro t
    have h : Measurable[ℱ t] (mkt.Dvec t) := (hDchar.2.1 t).measurable
    have : mkt.D t = fun ω => mkt.Dvec t ω 0 := by
      funext ω
      simp [Market.Dvec]
    rw [this]
    exact ((measurable_pi_apply 0).comp h).stronglyMeasurable
  -- the density version `G_t = exp(D_t - D_0 - (V_t - V_0))`
  set G : ℝ≥0 → Ω → ℝ := fun t ω =>
    Real.exp (mkt.D t ω - mkt.D 0 ω - (V mkt t ω - V mkt 0 ω)) with hGdef
  have hGm : ∀ t, StronglyMeasurable[ℱ t] (G t) := by
    intro t
    have hD0 : Measurable[ℱ t] (mkt.D 0) :=
      (hDad 0).measurable.mono (ℱ.mono (zero_le : (0 : ℝ≥0) ≤ t)) le_rfl
    have hV0 : Measurable[ℱ t] (V mkt 0) :=
      (hVad 0).measurable.mono (ℱ.mono (zero_le : (0 : ℝ≥0) ≤ t)) le_rfl
    exact (Real.measurable_exp.comp (((hDad t).measurable.sub hD0).sub
      ((hVad t).measurable.sub hV0))).stronglyMeasurable
  have hGpos : ∀ t ω, 0 < G t ω := fun _ _ => Real.exp_pos _
  -- `𝓔(V)_t = exp(V_t - V_0)` for all `t`, `P`-a.s.
  have hgood : ∀ᵐ ω ∂P, ∀ t,
      stochExp (V mkt) (fun _ _ => 0) t ω = Real.exp (V mkt t ω - V mkt 0 ω) := by
    filter_upwards [hVc] with ω hω
    exact stochExp_of_continuous (V mkt) ω hω.1
  -- `𝓔(M)_t = G_t` for all `t`, `P`-a.s.
  have hEM : ∀ᵐ ω ∂P, ∀ t, EM mkt M t ω = G t ω := by
    filter_upwards [hid, hgood] with ω h1 h2
    intro t
    have h := h1 t
    rw [h2 t] at h
    simp only [hGdef]
    rw [Real.exp_sub, Real.exp_sub, Real.exp_sub, h]
    have := Real.exp_pos (mkt.D 0 ω)
    have := Real.exp_pos (V mkt t ω)
    have := Real.exp_pos (V mkt 0 ω)
    field_simp
    rw [Real.exp_sub]
    field_simp
  have hdens : ∀ t A, MeasurableSet[ℱ t] A →
      Q A = ∫⁻ ω in A, ENNReal.ofReal (G t ω) ∂P := by
    intro t A hA
    rw [hdensEM t A hA]
    exact lintegral_congr_ae (ae_restrict_of_ae (hEM.mono fun ω h => by simp only [h t]))
  -- the fields: `U_t(y) = G_t U^V_t(y)` on the good set
  have hfield : ∀ ω, (∀ t, stochExp (V mkt) (fun _ _ => 0) t ω =
      Real.exp (V mkt t ω - V mkt 0 ω)) → ∀ t y,
      (U mkt p t y ω).toReal = G t ω * (UV mkt p t y ω).toReal := by
    intro ω hω t y
    simp only [U, UV, U0, hω t]
    split_ifs with hy hp
    · simp only [EReal.toReal_coe, hGdef]
      rw [show Real.exp (mkt.D t ω) = Real.exp (mkt.D t ω - mkt.D 0 ω - (V mkt t ω - V mkt 0 ω)) *
          Real.exp (mkt.D 0 ω) * Real.exp (V mkt t ω - V mkt 0 ω) by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring]
      ring
    · simp
    · simp
  -- the supermartingale / martingale transfer for every wealth process
  have key : ∀ (π : ℝ≥0 → Ω → Fin n → ℝ) (I : ℝ≥0 → Ω → ℝ) (x : ℝ),
      (Supermartingale (fun t ω => (U mkt p t (x * wealthExp mkt π I t ω) ω).toReal) ℱ P ↔
        Supermartingale (fun t ω => (UV mkt p t (x * wealthExp mkt π I t ω) ω).toReal) ℱ Q) ∧
      (Martingale (fun t ω => (U mkt p t (x * wealthExp mkt π I t ω) ω).toReal) ℱ P ↔
        Martingale (fun t ω => (UV mkt p t (x * wealthExp mkt π I t ω) ω).toReal) ℱ Q) := by
    intro π I x
    refine bayes ℱ P Q hnull G hGm hGpos hdens _ _ fun t => ?_
    filter_upwards [hgood] with ω hω
    exact hfield ω hω t _
  -- concavity and monotonicity of both fields
  have hcU : ∀ᵐ ω ∂P, ∀ t, ConcaveOn ℝ (Set.Ioi 0) (fun x => (U mkt p t x ω).toReal) ∧
      MonotoneOn (fun x => (U mkt p t x ω).toReal) (Set.Ioi 0) := by
    refine ae_of_all _ fun ω t => ?_
    obtain ⟨h1, h2⟩ := pow_div_concave (Real.exp (mkt.D t ω)) p (Real.exp_pos _).le hp0 hp1
    have heq : Set.EqOn (fun x : ℝ => Real.exp (mkt.D t ω) * x ^ p / p)
        (fun x => (U mkt p t x ω).toReal) (Set.Ioi 0) := by
      intro x hx
      have hx' : (0 : ℝ) < x := hx
      simp [U, hx']
    exact ⟨h1.congr heq, h2.congr heq⟩
  have hcV : ∀ᵐ ω ∂Q, ∀ t, ConcaveOn ℝ (Set.Ioi 0) (fun x => (UV mkt p t x ω).toReal) ∧
      MonotoneOn (fun x => (UV mkt p t x ω).toReal) (Set.Ioi 0) := by
    have : ∀ᵐ ω ∂P, ∀ t, ConcaveOn ℝ (Set.Ioi 0) (fun x => (UV mkt p t x ω).toReal) ∧
        MonotoneOn (fun x => (UV mkt p t x ω).toReal) (Set.Ioi 0) := by
      filter_upwards [hgood] with ω hω
      intro t
      obtain ⟨h1, h2⟩ := pow_div_concave
        (Real.exp (mkt.D 0 ω) * Real.exp (V mkt t ω - V mkt 0 ω)) p
        (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le hp0 hp1
      have heq : Set.EqOn
          (fun x : ℝ => Real.exp (mkt.D 0 ω) * Real.exp (V mkt t ω - V mkt 0 ω) * x ^ p / p)
          (fun x => (UV mkt p t x ω).toReal) (Set.Ioi 0) := by
        intro x hx
        have hx' : (0 : ℝ) < x := hx
        simp only [UV, U0, hx', if_true, hω t, EReal.toReal_coe]
        ring
      exact ⟨h1.congr heq, h2.congr heq⟩
    exact hQP.ae_le this
  unfold IsFIPP
  rw [hG]
  constructor
  · rintro ⟨h1, -, h3, h4⟩
    exact ⟨h1, hcV, fun x hx π hπ I hI => (key π I x).1.1 (h3 x hx π hπ I hI),
      fun x hx I hI => (key πstar I x).2.1 (h4 x hx I hI)⟩
  · rintro ⟨h1, -, h3, h4⟩
    exact ⟨h1, hcU, fun x hx π hπ I hI => (key π I x).1.2 (h3 x hx π hπ I hI),
      fun x hx I hI => (key πstar I x).2.2 (h4 x hx I hI)⟩
