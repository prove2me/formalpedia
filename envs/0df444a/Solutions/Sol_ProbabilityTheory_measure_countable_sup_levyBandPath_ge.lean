-- Prove2me | solution 1 for ProbabilityTheory.measure_countable_sup_levyBandPath_ge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T23:47:56.581567+00:00
-- url     : https://prove2.me/submissions/bd905315-76a7-4cb6-a780-e642f639614a

import Definitions.Def_LeanLevy_RandomMeasure_TimeSpacePoisson
import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpLaw
import Definitions.Def_LeanLevy_Processes_Cadlag
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Probability.Martingale.OptionalStopping
import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
import Theorems.Thm_ProbabilityTheory_martingale_levyBandVersion
import Theorems.Thm_ProbabilityTheory_levyBandVersion_ae_eq
open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal BigOperators
variable {Ω : Type} [MeasurableSpace Ω] {K : ℕ → Ω → ℕ}
  {X : ℕ → ℕ → Ω → ℝ × ℝ} {ν : Measure ℝ} [SigmaFinite ν] {μ : Measure Ω} {A : Set ℝ}

private lemma bandFun_toLp_ae_zero_off (hA : MeasurableSet A) (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1)
    (hAfin : ν A < ⊤) {s t : ℝ} {B : Set ℝ} (hB : Set.Ioc s t ⊆ B) :
    ∀ᵐ p ∂((volume : Measure ℝ).prod ν), p ∉ B ×ˢ (Set.univ : Set ℝ) →
      (memLp_two_bandFun hA hAsub hAfin s t).toLp
          ((Set.Ioc s t ×ˢ A).indicator fun q : ℝ × ℝ => q.2) p = 0 := by
  filter_upwards [MemLp.coeFn_toLp (memLp_two_bandFun hA hAsub hAfin s t)] with p hp hpB
  rw [hp]
  apply Set.indicator_of_notMem
  intro hmem
  exact hpB ⟨hB hmem.1, Set.mem_univ _⟩

/-- The compensated band integral over `(0, t]` is almost-everywhere strongly measurable with respect
to the evaluation sigma-algebra of the prefix region `(-∞, t] × ℝ`. -/
private lemma aestronglyMeasurable_levyBandPath_prefix [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ)
    (hA : MeasurableSet A) (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1) (hAfin : ν A < ⊤) (t : ℝ≥0) :
    AEStronglyMeasurable[prmEvalSigma K X (volume.prod ν) (Set.Iic (t : ℝ) ×ˢ Set.univ)]
      (compensatedPoissonIntegral hd ((memLp_two_bandFun hA hAsub hAfin 0 (t : ℝ)).toLp _)) μ :=
  aestronglyMeasurable_compensatedPoissonIntegral_prmEvalSigma hd
    (measurableSet_Iic.prod MeasurableSet.univ)
    (bandFun_toLp_ae_zero_off hA hAsub hAfin Set.Ioc_subset_Iic_self)
private lemma integrable_levyBandVersion [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (hA : MeasurableSet A) (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1) (hAfin : ν A < ⊤) (t : ℝ≥0) :
    Integrable (levyBandVersion hd hν hA hAsub hAfin t) μ := by
  simp only [levyBandVersion]
  exact ((Lp.memLp (compensatedPoissonIntegral hd
    ((memLp_two_bandFun hA hAsub hAfin 0 (t : ℝ)).toLp _))).integrable one_le_two).congr
    (aestronglyMeasurable_levyBandPath_prefix hd hA hAsub hAfin t).ae_eq_mk
private theorem eLpNorm_sq_bandFun {ν : Measure ℝ} [SigmaFinite ν] {C : Set ℝ}
    (hC : MeasurableSet C) (s t : ℝ) :
    (eLpNorm ((Set.Ioc s t ×ˢ C).indicator fun p : ℝ × ℝ => p.2) 2 (volume.prod ν)) ^ 2
      = ENNReal.ofReal (t - s) * ∫⁻ x in C, ENNReal.ofReal (x ^ 2) ∂ν := by
  have hnorm :
      (eLpNorm ((Set.Ioc s t ×ˢ C).indicator fun p : ℝ × ℝ => p.2) 2 (volume.prod ν)) ^ 2
        = ∫⁻ p, ‖(Set.Ioc s t ×ˢ C).indicator (fun q : ℝ × ℝ => q.2) p‖ₑ ^ (2 : ℝ)
            ∂(volume.prod ν) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
      show ((2 : ℝ≥0∞).toReal) = (2 : ℝ) from by norm_num,
      ← ENNReal.rpow_natCast (_ ^ (1 / (2 : ℝ))) 2, ← ENNReal.rpow_mul,
      show (1 / (2 : ℝ)) * ((2 : ℕ) : ℝ) = 1 from by norm_num, ENNReal.rpow_one]
  have hband :
      ∫⁻ p, ‖(Set.Ioc s t ×ˢ C).indicator (fun q : ℝ × ℝ => q.2) p‖ₑ ^ (2 : ℝ)
          ∂(volume.prod ν)
        = ∫⁻ p in Set.Ioc s t ×ˢ C, ENNReal.ofReal (p.2 ^ 2) ∂(volume.prod ν) := by
    rw [← lintegral_indicator (measurableSet_Ioc.prod hC)]
    refine lintegral_congr fun p => ?_
    by_cases hp : p ∈ Set.Ioc s t ×ˢ C
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, Real.enorm_eq_ofReal_abs,
        ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
      congr 1
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast, sq_abs]
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp, enorm_zero,
        ENNReal.zero_rpow_of_pos (by norm_num)]
  have htonelli :
      ∫⁻ p in Set.Ioc s t ×ˢ C, ENNReal.ofReal (p.2 ^ 2) ∂(volume.prod ν)
        = ENNReal.ofReal (t - s) * ∫⁻ x in C, ENNReal.ofReal (x ^ 2) ∂ν := by
    rw [← Measure.prod_restrict,
      lintegral_prod (fun p : ℝ × ℝ => ENNReal.ofReal (p.2 ^ 2))
        (measurable_snd.pow_const 2).ennreal_ofReal.aemeasurable]
    have hinner : ∀ r : ℝ,
        ∫⁻ x, ENNReal.ofReal ((r, x).2 ^ 2) ∂(ν.restrict C)
          = ∫⁻ x in C, ENNReal.ofReal (x ^ 2) ∂ν := fun _ => rfl
    rw [lintegral_congr hinner, setLIntegral_const, Real.volume_Ioc, mul_comm]
  exact hnorm.trans (hband.trans htonelli)

private lemma lintegral_setOf_sq_lt_top (hA : MeasurableSet A) (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1)
    (hν : IsLevyMeasure ν) : ∫⁻ x in A, ENNReal.ofReal (x ^ 2) ∂ν < ⊤ := by
  refine lt_of_le_of_lt ?_ hν.2
  rw [← lintegral_indicator hA]
  refine lintegral_mono fun x => ?_
  by_cases hx : x ∈ A
  · rw [Set.indicator_of_mem hx]
    obtain ⟨h1, h2⟩ := hAsub hx
    exact ENNReal.ofReal_le_ofReal (le_min (by nlinarith) le_rfl)
  · rw [Set.indicator_of_notMem hx]; exact zero_le

/-- The function `x ↦ x²` is `ν`-integrable on a band `A ⊆ (-1, 1)`. -/
private lemma integrableOn_sq (hA : MeasurableSet A) (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1)
    (hν : IsLevyMeasure ν) : IntegrableOn (fun x : ℝ => x ^ 2) A ν := by
  refine ⟨(by fun_prop : Measurable (fun x : ℝ => x ^ 2)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => sq_nonneg x)]
  exact lintegral_setOf_sq_lt_top hA hAsub hν

/-- The `ENNReal.ofReal` of the Bochner integral of `x²` over a band equals its lower integral. -/
private lemma ofReal_integral_sq (hA : MeasurableSet A) (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1)
    (hν : IsLevyMeasure ν) :
    ENNReal.ofReal (∫ x in A, x ^ 2 ∂ν) = ∫⁻ x in A, ENNReal.ofReal (x ^ 2) ∂ν :=
  ofReal_integral_eq_lintegral_ofReal (integrableOn_sq hA hAsub hν)
    (ae_of_all _ fun x => sq_nonneg x)

/-- The `ℕ`-grid filtration obtained by restricting `prmFiltration` along a monotone reindexing. -/
private noncomputable def gridFiltration
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ)
    (u : ℕ → ℝ≥0) (hu : Monotone u) : MeasureTheory.Filtration ℕ ‹MeasurableSpace Ω› where
  seq k := prmFiltration K X ν hd.measurable_count hd.measurable_point (u k)
  mono' _ _ hij := (prmFiltration K X ν hd.measurable_count hd.measurable_point).mono (hu hij)
  le' k := (prmFiltration K X ν hd.measurable_count hd.measurable_point).le (u k)

/-- The absolute value of the compensated band martingale, sampled along a monotone `ℕ`-grid, is a
nonnegative submartingale for the grid filtration (`|M| = M ⊔ (-M)` of a martingale). -/
private lemma submartingale_abs_levyBandVersion_grid [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (hA : MeasurableSet A) (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1) (hAfin : ν A < ⊤)
    {u : ℕ → ℝ≥0} (hu : Monotone u) :
    MeasureTheory.Submartingale
      (fun k ω => |levyBandVersion hd hν hA hAsub hAfin (u k) ω|)
      (gridFiltration hd u hu) μ := by
  have hM := martingale_levyBandVersion hd hν hA hAsub hAfin
  have hMN : MeasureTheory.Martingale
      (fun k => levyBandVersion hd hν hA hAsub hAfin (u k)) (gridFiltration hd u hu) μ :=
    ⟨fun k => hM.1 (u k), fun i j hij => hM.2 (u i) (u j) (hu hij)⟩
  have habs : ∀ a : ℝ, a ⊔ -a = |a| := fun a => by
    rcases le_total 0 a with h | h
    · rw [sup_eq_left.mpr (by linarith), abs_of_nonneg h]
    · rw [sup_eq_right.mpr (by linarith), abs_of_nonpos h]
  have heq : ((fun k => levyBandVersion hd hν hA hAsub hAfin (u k))
        ⊔ -(fun k => levyBandVersion hd hν hA hAsub hAfin (u k)))
      = fun k ω => |levyBandVersion hd hν hA hAsub hAfin (u k) ω| := by
    funext k ω
    show levyBandVersion hd hν hA hAsub hAfin (u k) ω
        ⊔ -(levyBandVersion hd hν hA hAsub hAfin (u k) ω) = _
    exact habs _
  have hsup := hMN.submartingale.sup hMN.neg.submartingale
  rw [heq] at hsup
  exact hsup

/-- The second moment of the compensated band path at time `v` is `v · ∫_A x² dν`. -/
private lemma eLpNorm_two_sq_levyBandVersion [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (hA : MeasurableSet A) (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1) (hAfin : ν A < ⊤) (v : ℝ≥0) :
    (eLpNorm (levyBandVersion hd hν hA hAsub hAfin v) 2 μ) ^ 2
      = ENNReal.ofReal ((v : ℝ) * ∫ x in A, x ^ 2 ∂ν) := by
  have hae : levyBandVersion hd hν hA hAsub hAfin v
      =ᵐ[μ] compensatedPoissonIntegral hd ((memLp_two_bandFun hA hAsub hAfin 0 (v : ℝ)).toLp _) :=
    (aestronglyMeasurable_levyBandPath_prefix hd hA hAsub hAfin v).ae_eq_mk.symm
  rw [eLpNorm_congr_ae hae, eLpNorm_compensatedPoissonIntegral,
    eLpNorm_congr_ae (MemLp.coeFn_toLp _), eLpNorm_sq_bandFun hA 0 (v : ℝ), sub_zero,
    ← ofReal_integral_sq hA hAsub hν, ← ENNReal.ofReal_mul (NNReal.coe_nonneg v)]

/-- On a probability space, the mean absolute value of the compensated band path at time `v` is
bounded by `√(v · ∫_A x² dν)` (the `L¹ ≤ L²` bound composed with the second-moment isometry). -/
private lemma integral_abs_levyBandVersion_le [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (hA : MeasurableSet A) (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1) (hAfin : ν A < ⊤) (v : ℝ≥0) :
    ∫ ω, |levyBandVersion hd hν hA hAsub hAfin v ω| ∂μ
      ≤ Real.sqrt ((v : ℝ) * ∫ x in A, x ^ 2 ∂ν) := by
  have haesm : AEStronglyMeasurable (levyBandVersion hd hν hA hAsub hAfin v) μ :=
    (integrable_levyBandVersion hd hν hA hAsub hAfin v).aestronglyMeasurable
  have hae : levyBandVersion hd hν hA hAsub hAfin v
      =ᵐ[μ] compensatedPoissonIntegral hd ((memLp_two_bandFun hA hAsub hAfin 0 (v : ℝ)).toLp _) :=
    (aestronglyMeasurable_levyBandPath_prefix hd hA hAsub hAfin v).ae_eq_mk.symm
  have h2ne : eLpNorm (levyBandVersion hd hν hA hAsub hAfin v) 2 μ ≠ ⊤ := by
    rw [eLpNorm_congr_ae hae]; exact Lp.eLpNorm_ne_top _
  have h1 : ∫ ω, |levyBandVersion hd hν hA hAsub hAfin v ω| ∂μ
      = (eLpNorm (levyBandVersion hd hν hA hAsub hAfin v) 1 μ).toReal := by
    simp_rw [← Real.norm_eq_abs]
    rw [integral_norm_eq_lintegral_enorm haesm, ← eLpNorm_one_eq_lintegral_enorm]
  have hmono : eLpNorm (levyBandVersion hd hν hA hAsub hAfin v) 1 μ
      ≤ eLpNorm (levyBandVersion hd hν hA hAsub hAfin v) 2 μ :=
    eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) haesm
  have hsqrt : (eLpNorm (levyBandVersion hd hν hA hAsub hAfin v) 2 μ).toReal
      = Real.sqrt ((v : ℝ) * ∫ x in A, x ^ 2 ∂ν) := by
    have hreal : (eLpNorm (levyBandVersion hd hν hA hAsub hAfin v) 2 μ).toReal ^ 2
        = (v : ℝ) * ∫ x in A, x ^ 2 ∂ν := by
      rw [← ENNReal.toReal_pow, eLpNorm_two_sq_levyBandVersion hd hν hA hAsub hAfin v,
        ENNReal.toReal_ofReal (mul_nonneg (NNReal.coe_nonneg v)
          (integral_nonneg fun x => sq_nonneg x))]
    rw [← hreal, Real.sqrt_sq ENNReal.toReal_nonneg]
  rw [h1, ← hsqrt]
  exact ENNReal.toReal_mono h2ne hmono

/-- **Single finite grid.** For a finite set `F ⊆ [0, T]` of times, the measure of the event that the
compensated band path exceeds `ε` at some time in `F` is bounded by `√(T · ∫_A x² dν) / ε`. -/
private lemma measure_finset_sup_levyBandVersion_ge [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (hA : MeasurableSet A) (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1) (hAfin : ν A < ⊤)
    {T : ℝ} (_hT : 0 ≤ T) {ε : ℝ≥0} (hε : 0 < ε) (F : Finset ℝ≥0)
    (hFT : ∀ v ∈ F, (v : ℝ) ≤ T) :
    μ {ω | ∃ v ∈ F, (ε : ℝ) ≤ |levyBandVersion hd hν hA hAsub hAfin v ω|}
      ≤ ENNReal.ofReal (Real.sqrt (T * ∫ x in A, x ^ 2 ∂ν)) / ε := by
  rcases F.eq_empty_or_nonempty with hFe | hFne
  · subst hFe
    simp only [Finset.notMem_empty, false_and, exists_false, Set.setOf_false, measure_empty]
    exact zero_le
  set N := F.card with hN
  have hmpos : 0 < N := Finset.card_pos.mpr hFne
  have hlt : ∀ k : ℕ, min k (N - 1) < N := fun k => by omega
  let u : ℕ → ℝ≥0 := fun k => F.orderEmbOfFin hN.symm ⟨min k (N - 1), hlt k⟩
  have hmemF : ∀ k, u k ∈ F := fun k => Finset.orderEmbOfFin_mem F hN.symm ⟨min k (N - 1), hlt k⟩
  have hmono : Monotone u := fun i j hij =>
    (F.orderEmbOfFin hN.symm).monotone (by simp only [Fin.mk_le_mk]; omega)
  have hevent_eq :
      {ω | (ε : ℝ) ≤ (Finset.range (N - 1 + 1)).sup' Finset.nonempty_range_add_one
            (fun k => |levyBandVersion hd hν hA hAsub hAfin (u k) ω|)}
        = {ω | ∃ v ∈ F, (ε : ℝ) ≤ |levyBandVersion hd hν hA hAsub hAfin v ω|} := by
    ext ω
    simp only [Set.mem_setOf_eq, Finset.le_sup'_iff, Finset.mem_range]
    constructor
    · rintro ⟨k, _, hle⟩
      exact ⟨u k, hmemF k, hle⟩
    · rintro ⟨v, hv, hle⟩
      have hmem : v ∈ Set.range (F.orderEmbOfFin hN.symm) := by
        rw [Finset.range_orderEmbOfFin]; exact Finset.mem_coe.mpr hv
      obtain ⟨i, hi⟩ := hmem
      refine ⟨(i : ℕ), by have := i.2; omega, ?_⟩
      have hfin : (⟨min (i : ℕ) (N - 1), hlt (i : ℕ)⟩ : Fin N) = i := by
        apply Fin.ext
        show min (i : ℕ) (N - 1) = (i : ℕ)
        have := i.2; omega
      have huv : u (i : ℕ) = v := by
        show F.orderEmbOfFin hN.symm ⟨min (i : ℕ) (N - 1), hlt (i : ℕ)⟩ = v
        rw [hfin]; exact hi
      rw [huv]; exact hle
  have hb : (∫ ω in {ω | ∃ v ∈ F, (ε : ℝ) ≤ |levyBandVersion hd hν hA hAsub hAfin v ω|},
        |levyBandVersion hd hν hA hAsub hAfin (u (N - 1)) ω| ∂μ)
      ≤ Real.sqrt (T * ∫ x in A, x ^ 2 ∂ν) :=
    calc (∫ ω in {ω | ∃ v ∈ F, (ε : ℝ) ≤ |levyBandVersion hd hν hA hAsub hAfin v ω|},
            |levyBandVersion hd hν hA hAsub hAfin (u (N - 1)) ω| ∂μ)
        ≤ ∫ ω, |levyBandVersion hd hν hA hAsub hAfin (u (N - 1)) ω| ∂μ :=
          setIntegral_le_integral
            (integrable_levyBandVersion hd hν hA hAsub hAfin (u (N - 1))).abs
            (ae_of_all _ fun ω => abs_nonneg _)
      _ ≤ Real.sqrt ((u (N - 1) : ℝ) * ∫ x in A, x ^ 2 ∂ν) :=
          integral_abs_levyBandVersion_le hd hν hA hAsub hAfin (u (N - 1))
      _ ≤ Real.sqrt (T * ∫ x in A, x ^ 2 ∂ν) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right (hFT _ (hmemF (N - 1)))
            (integral_nonneg fun x => sq_nonneg x))
  have hmax := maximal_ineq (submartingale_abs_levyBandVersion_grid hd hν hA hAsub hAfin hmono)
    (fun _ _ => abs_nonneg _) (ε := ε) (N - 1)
  rw [hevent_eq] at hmax
  refine (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.coe_ne_zero.mpr hε.ne'))
    (Or.inl ENNReal.coe_ne_top)).mpr ?_
  rw [mul_comm]
  exact hmax.trans (ENNReal.ofReal_le_ofReal hb)

/-- **Maximal inequality over a countable grid.** For a band `A ⊆ (-1, 1)` of finite `ν`-mass and a
countable set of times `D ⊆ [0, T]`, the measure of the event that the compensated band path
`levyBandPath` exceeds a level `ε` in absolute value at some time in `D` is bounded by
`√(T · ∫_A x² dν) / ε`. The event is transferred to the adapted representative `levyBandVersion`
(equal almost everywhere at each of the countably many grid times), then bounded through the finite
maximal inequality on each finite sub-grid and continuity of measure from below. -/
theorem solution [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (hA : MeasurableSet A) (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1) (hAfin : ν A < ⊤)
    {T : ℝ} (hT : 0 ≤ T) {D : Set ℝ} (hD : D.Countable) (hDT : D ⊆ Set.Icc 0 T)
    {ε : ℝ≥0} (hε : 0 < ε) :
    μ {ω | ∃ t ∈ D, (ε : ℝ) ≤ |levyBandPath K X ν A t ω|}
      ≤ ENNReal.ofReal (Real.sqrt (T * ∫ x in A, x ^ 2 ∂ν)) / ε := by
  rcases Set.eq_empty_or_nonempty D with hDempty | hDne
  · subst hDempty
    simp only [Set.mem_empty_iff_false, false_and, exists_false, Set.setOf_false, measure_empty]
    exact zero_le
  obtain ⟨e, hDe⟩ := hD.exists_eq_range hDne
  -- almost-everywhere transfer between the path and its adapted representative at each grid time
  have htrans : ∀ᵐ ω ∂μ, ∀ n : ℕ,
      levyBandVersion hd hν hA hAsub hAfin ((e n).toNNReal) ω
        = levyBandPath K X ν A (e n) ω := by
    rw [ae_all_iff]
    intro n
    have hen : e n ∈ D := by rw [hDe]; exact Set.mem_range_self n
    filter_upwards [levyBandVersion_ae_eq hd hν hA hAsub hAfin ((e n).toNNReal)] with ω hω
    rw [hω, Real.coe_toNNReal (e n) (hDT hen).1]
  -- the countable version-event, bounded through finite sub-grids
  have key : μ {ω | ∃ n : ℕ, (ε : ℝ) ≤ |levyBandVersion hd hν hA hAsub hAfin ((e n).toNNReal) ω|}
      ≤ ENNReal.ofReal (Real.sqrt (T * ∫ x in A, x ^ 2 ∂ν)) / ε := by
    have hmono : Monotone (fun N : ℕ =>
        {ω | ∃ n ∈ Finset.range (N + 1),
          (ε : ℝ) ≤ |levyBandVersion hd hν hA hAsub hAfin ((e n).toNNReal) ω|}) := by
      intro N M hNM ω hω
      obtain ⟨n, hn, hle⟩ := hω
      exact ⟨n, Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hn) (by omega)), hle⟩
    have hunion : {ω | ∃ n : ℕ, (ε : ℝ) ≤ |levyBandVersion hd hν hA hAsub hAfin ((e n).toNNReal) ω|}
        = ⋃ N : ℕ, {ω | ∃ n ∈ Finset.range (N + 1),
            (ε : ℝ) ≤ |levyBandVersion hd hν hA hAsub hAfin ((e n).toNNReal) ω|} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨n, hle⟩
        exact ⟨n, n, Finset.self_mem_range_succ n, hle⟩
      · rintro ⟨_, n, _, hle⟩
        exact ⟨n, hle⟩
    rw [hunion, hmono.measure_iUnion]
    refine iSup_le fun N => ?_
    have heq : {ω | ∃ n ∈ Finset.range (N + 1),
          (ε : ℝ) ≤ |levyBandVersion hd hν hA hAsub hAfin ((e n).toNNReal) ω|}
        = {ω | ∃ v ∈ (Finset.range (N + 1)).image (fun n => (e n).toNNReal),
            (ε : ℝ) ≤ |levyBandVersion hd hν hA hAsub hAfin v ω|} := by
      ext ω
      simp only [Set.mem_setOf_eq, Finset.mem_image]
      constructor
      · rintro ⟨n, hn, hle⟩
        exact ⟨(e n).toNNReal, ⟨n, hn, rfl⟩, hle⟩
      · rintro ⟨v, ⟨n, hn, rfl⟩, hle⟩
        exact ⟨n, hn, hle⟩
    rw [heq]
    refine measure_finset_sup_levyBandVersion_ge hd hν hA hAsub hAfin hT hε _ ?_
    intro v hv
    obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hv
    have hen : e n ∈ D := by rw [hDe]; exact Set.mem_range_self n
    rw [Real.coe_toNNReal (e n) (hDT hen).1]
    exact (hDT hen).2
  -- transfer the path event to the version event and conclude
  refine le_trans ?_ key
  have hsubset : {ω | ∃ t ∈ D, (ε : ℝ) ≤ |levyBandPath K X ν A t ω|}
      ⊆ {ω | ∃ n : ℕ, (ε : ℝ) ≤ |levyBandVersion hd hν hA hAsub hAfin ((e n).toNNReal) ω|}
        ∪ {ω | ¬ ∀ n : ℕ, levyBandVersion hd hν hA hAsub hAfin ((e n).toNNReal) ω
            = levyBandPath K X ν A (e n) ω} := by
    intro ω hω
    by_cases hG : ∀ n : ℕ, levyBandVersion hd hν hA hAsub hAfin ((e n).toNNReal) ω
        = levyBandPath K X ν A (e n) ω
    · left
      obtain ⟨t, htD, hle⟩ := hω
      rw [hDe] at htD
      obtain ⟨n, rfl⟩ := htD
      exact ⟨n, by rw [hG n]; exact hle⟩
    · exact Or.inr hG
  calc μ {ω | ∃ t ∈ D, (ε : ℝ) ≤ |levyBandPath K X ν A t ω|}
      ≤ μ ({ω | ∃ n : ℕ, (ε : ℝ) ≤ |levyBandVersion hd hν hA hAsub hAfin ((e n).toNNReal) ω|}
          ∪ {ω | ¬ ∀ n : ℕ, levyBandVersion hd hν hA hAsub hAfin ((e n).toNNReal) ω
              = levyBandPath K X ν A (e n) ω}) := measure_mono hsubset
    _ ≤ μ {ω | ∃ n : ℕ, (ε : ℝ) ≤ |levyBandVersion hd hν hA hAsub hAfin ((e n).toNNReal) ω|}
          + μ {ω | ¬ ∀ n : ℕ, levyBandVersion hd hν hA hAsub hAfin ((e n).toNNReal) ω
              = levyBandPath K X ν A (e n) ω} := measure_union_le _ _
    _ = μ {ω | ∃ n : ℕ, (ε : ℝ) ≤ |levyBandVersion hd hν hA hAsub hAfin ((e n).toNNReal) ω|} := by
        rw [ae_iff.mp htrans, add_zero]

