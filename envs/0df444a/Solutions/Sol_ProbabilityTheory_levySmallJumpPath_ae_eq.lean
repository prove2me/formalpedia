-- Prove2me | solution 1 for ProbabilityTheory.levySmallJumpPath_ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T23:45:39.705185+00:00
-- url     : https://prove2.me/submissions/78cf9116-ca4d-4980-b3da-04a284a9e10e

import Definitions.Def_LeanLevy_RandomMeasure_TimeSpacePoisson
import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpLaw
import Definitions.Def_LeanLevy_Processes_Cadlag
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Probability.Martingale.OptionalStopping
import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
import Theorems.Thm_ProbabilityTheory_levyBandPath_ae_eq_compensated
import Theorems.Thm_ProbabilityTheory_eLpNorm_smallJumpBand_sub_bandFun
import Theorems.Thm_ProbabilityTheory_levyTruncationSeq_spec
import Theorems.Thm_ProbabilityTheory_ae_mem_levySmallJumpGoodSet
import Theorems.Thm_ProbabilityTheory_tendsto_levyBandPath_levySmallJumpPath
open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal BigOperators
variable {Ω : Type} [MeasurableSpace Ω] {K : ℕ → Ω → ℕ}
  {X : ℕ → ℕ → Ω → ℝ × ℝ} {ν : Measure ℝ} [SigmaFinite ν] {μ : Measure Ω}

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

private noncomputable def levyAnnulusElement [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (t : ℝ) (j : ℕ) : Lp ℝ 2 μ :=
  compensatedPoissonIntegral hd ((memLp_two_bandFun
    (measurableSet_levyAnnulus (levyTruncationSeq hν j))
    (levyAnnulus_subset (levyTruncationSeq hν j))
    (levyAnnulus_finite_mass hν (levyTruncationSeq hν j)) 0 t).toLp _)

/-- The pathwise annulus approximant agrees almost everywhere with the truncation element (the
Task-3 `L²` anchor at the annulus band). -/
private lemma levyBandPath_ae_eq_levyAnnulusElement [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    {t : ℝ} (ht : 0 ≤ t) (j : ℕ) :
    (fun ω => levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν j)) t ω)
      =ᵐ[μ] levyAnnulusElement hd hν t j :=
  levyBandPath_ae_eq_compensated hd (measurableSet_levyAnnulus (levyTruncationSeq hν j))
    (levyAnnulus_subset (levyTruncationSeq hν j))
    (levyAnnulus_finite_mass hν (levyTruncationSeq hν j)) ht

/-- **`L²` convergence of the truncation elements.** The `L²(μ)` distance from the truncation
element at step `j` to the compensated small-jump integral is the seminorm of the band indicator
over the complementary slice `(0, t] × ((-1, 1) \ levyAnnulus (levyTruncationSeq hν j))`, whose
square is at most `t · 16⁻ʲ`; hence the distance vanishes as `j → ∞`. -/
private lemma tendsto_eLpNorm_levyAnnulusElement_sub [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun j => eLpNorm
        (⇑(levyAnnulusElement hd hν t j) - ⇑(levyCompensatedSmallJump hd hν t)) 2 μ)
      atTop (𝓝 0) := by
  -- the distance flips to the `Lp` difference of the elements
  have hcoe : ∀ j : ℕ,
      eLpNorm (⇑(levyAnnulusElement hd hν t j) - ⇑(levyCompensatedSmallJump hd hν t)) 2 μ
        = eLpNorm (⇑(levyCompensatedSmallJump hd hν t - levyAnnulusElement hd hν t j)) 2 μ := by
    intro j
    rw [← neg_sub (⇑(levyCompensatedSmallJump hd hν t)) (⇑(levyAnnulusElement hd hν t j)),
      eLpNorm_neg]
    exact (eLpNorm_congr_ae (Lp.coeFn_sub _ _)).symm
  -- the `Lp` distance is the complementary-slice seminorm
  have hdist : ∀ j : ℕ,
      eLpNorm (⇑(levyCompensatedSmallJump hd hν t - levyAnnulusElement hd hν t j)) 2 μ
        = eLpNorm ((Set.Ioc 0 t ×ˢ (Set.Ioo (-1 : ℝ) 1
              \ levyAnnulus (levyTruncationSeq hν j))).indicator fun p : ℝ × ℝ => p.2) 2
            (volume.prod ν) := fun j =>
    eLpNorm_smallJumpBand_sub_bandFun hd hν 0 t
      (measurableSet_levyAnnulus (levyTruncationSeq hν j))
      (levyAnnulus_subset (levyTruncationSeq hν j))
      (levyAnnulus_finite_mass hν (levyTruncationSeq hν j))
  -- squared distance bounded by the geometric tail moment
  have hsq_le : ∀ j : ℕ,
      (eLpNorm (⇑(levyAnnulusElement hd hν t j)
          - ⇑(levyCompensatedSmallJump hd hν t)) 2 μ) ^ 2
        ≤ ENNReal.ofReal t * (16 : ℝ≥0∞)⁻¹ ^ j := by
    intro j
    rw [hcoe j, hdist j,
      eLpNorm_sq_bandFun (measurableSet_Ioo.diff (measurableSet_levyAnnulus _)) 0 t, sub_zero]
    exact mul_le_mul_right ((levyTruncationSeq_spec hν).2 j) _
  have hne : ∀ j : ℕ,
      eLpNorm (⇑(levyAnnulusElement hd hν t j) - ⇑(levyCompensatedSmallJump hd hν t)) 2 μ ≠ ⊤ :=
    fun j => by rw [hcoe j]; exact Lp.eLpNorm_ne_top _
  -- the real-valued distances are squeezed by the geometric envelope `√t · 4⁻ʲ`
  have htoReal_le : ∀ j : ℕ,
      (eLpNorm (⇑(levyAnnulusElement hd hν t j)
          - ⇑(levyCompensatedSmallJump hd hν t)) 2 μ).toReal
        ≤ Real.sqrt t * ((4 : ℝ)⁻¹) ^ j := by
    intro j
    have hbne : ENNReal.ofReal t * (16 : ℝ≥0∞)⁻¹ ^ j ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.pow_lt_top (ENNReal.inv_lt_top.mpr (by norm_num))).ne
    have hsq' : ((eLpNorm (⇑(levyAnnulusElement hd hν t j)
          - ⇑(levyCompensatedSmallJump hd hν t)) 2 μ).toReal) ^ 2
        ≤ t * ((16 : ℝ)⁻¹) ^ j := by
      rw [← ENNReal.toReal_pow]
      calc ((eLpNorm (⇑(levyAnnulusElement hd hν t j)
              - ⇑(levyCompensatedSmallJump hd hν t)) 2 μ) ^ 2).toReal
          ≤ (ENNReal.ofReal t * (16 : ℝ≥0∞)⁻¹ ^ j).toReal :=
            ENNReal.toReal_mono hbne (hsq_le j)
        _ = t * ((16 : ℝ)⁻¹) ^ j := by
            rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal ht, ENNReal.toReal_pow,
              ENNReal.toReal_inv]
            norm_num
    have hsqrt16 : Real.sqrt (((16 : ℝ)⁻¹) ^ j) = ((4 : ℝ)⁻¹) ^ j := by
      have h4 : (((4 : ℝ)⁻¹) ^ j) ^ 2 = ((16 : ℝ)⁻¹) ^ j := by
        rw [← pow_mul, mul_comm, pow_mul, show ((4 : ℝ)⁻¹) ^ 2 = (16 : ℝ)⁻¹ by norm_num]
      rw [← h4, Real.sqrt_sq (by positivity)]
    calc (eLpNorm (⇑(levyAnnulusElement hd hν t j)
            - ⇑(levyCompensatedSmallJump hd hν t)) 2 μ).toReal
        = Real.sqrt (((eLpNorm (⇑(levyAnnulusElement hd hν t j)
            - ⇑(levyCompensatedSmallJump hd hν t)) 2 μ).toReal) ^ 2) :=
          (Real.sqrt_sq ENNReal.toReal_nonneg).symm
      _ ≤ Real.sqrt (t * ((16 : ℝ)⁻¹) ^ j) := Real.sqrt_le_sqrt hsq'
      _ = Real.sqrt t * ((4 : ℝ)⁻¹) ^ j := by rw [Real.sqrt_mul ht, hsqrt16]
  have hgeo : Tendsto (fun j : ℕ => Real.sqrt t * ((4 : ℝ)⁻¹) ^ j) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ (4 : ℝ)⁻¹) (by norm_num)).const_mul (Real.sqrt t)
    simpa using h
  have htoReal : Tendsto (fun j => (eLpNorm (⇑(levyAnnulusElement hd hν t j)
      - ⇑(levyCompensatedSmallJump hd hν t)) 2 μ).toReal) atTop (𝓝 0) :=
    squeeze_zero (fun j => ENNReal.toReal_nonneg) htoReal_le hgeo
  exact (ENNReal.tendsto_toReal_iff hne (by simp)).mp (by simpa using htoReal)

/-- **The compensated small-jump path is a modification of the small-jump integral.** For each
fixed time `t ≥ 0`, the compensated small-jump path `levySmallJumpPath hd hν t` agrees
`μ`-almost everywhere with the `L²` small-jump element `levyCompensatedSmallJump hd hν t`.

This is a per-time almost-everywhere identification: the null set may depend on `t`, and no
process-level (uniform-in-`t`) statement is claimed. The truncation elements converge to the
small-jump element in `L²(μ)`, hence in measure, hence almost everywhere along a subsequence
`ns`; on the intersection of the good set with the countably many almost-sure events, the annulus
paths along `ns` converge to both `levySmallJumpPath hd hν t ω` and
`levyCompensatedSmallJump hd hν t ω`, and limits in `ℝ` are unique. -/
theorem solution [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    {t : ℝ} (ht : 0 ≤ t) :
    levySmallJumpPath hd hν t =ᵐ[μ] levyCompensatedSmallJump hd hν t := by
  -- `L²` convergence upgrades to convergence in measure, hence a.e. along a subsequence
  have hTIM : TendstoInMeasure μ (fun j => ⇑(levyAnnulusElement hd hν t j)) atTop
      ⇑(levyCompensatedSmallJump hd hν t) :=
    tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
      (fun j => Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
      (tendsto_eLpNorm_levyAnnulusElement_sub hd hν ht)
  obtain ⟨ns, hns, hae⟩ := hTIM.exists_seq_tendsto_ae
  -- glue the countably many almost-sure events
  have hpath : ∀ᵐ ω ∂μ, ∀ j : ℕ,
      levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν j)) t ω
        = levyAnnulusElement hd hν t j ω := by
    rw [ae_all_iff]
    exact fun j => levyBandPath_ae_eq_levyAnnulusElement hd hν ht j
  filter_upwards [ae_mem_levySmallJumpGoodSet hd hν, hpath, hae] with ω hgood hp hconv
  -- the annulus paths along the subsequence converge to the compensated small-jump path ...
  have h1 : Tendsto (fun i => levyBandPath K X ν
      (levyAnnulus (levyTruncationSeq hν (ns i))) t ω) atTop
      (𝓝 (levySmallJumpPath hd hν t ω)) :=
    (tendsto_levyBandPath_levySmallJumpPath hd hν hgood ht).comp hns.tendsto_atTop
  -- ... and to the small-jump element, through the per-`j` a.e. identifications
  have h2 : Tendsto (fun i => levyBandPath K X ν
      (levyAnnulus (levyTruncationSeq hν (ns i))) t ω) atTop
      (𝓝 (levyCompensatedSmallJump hd hν t ω)) :=
    hconv.congr fun i => (hp (ns i)).symm
  exact tendsto_nhds_unique h1 h2


