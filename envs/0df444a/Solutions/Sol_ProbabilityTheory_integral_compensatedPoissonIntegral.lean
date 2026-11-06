-- Prove2me | solution 1 for ProbabilityTheory.integral_compensatedPoissonIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T04:10:41.837519+00:00
-- url     : https://prove2.me/submissions/9a4857d8-25d7-42b7-aea8-23c6ea91477d

import Definitions.Def_LeanLevy_RandomMeasure_PoissonCompensated
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Moments.Variance
open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal NNReal Topology
namespace ProbabilityTheory
variable {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω]
  {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
  {f g : E → ℝ} {m : Measure E} [SigmaFinite m] [Nonempty E]
  {μ : Measure Ω} {k : ℕ}
private theorem hasSum_setIntegral_prmPiece {φ : E → ℝ} (hφ : Integrable φ m) :
    HasSum (fun k => ∫ x in prmPiece m k, φ x ∂m) (∫ x, φ x ∂m) := by
  have hunion : IntegrableOn φ (⋃ k, prmPiece m k) m := by
    rw [iUnion_prmPiece]; exact hφ.integrableOn
  have h := hasSum_integral_iUnion (fun k => measurableSet_prmPiece) pairwise_disjoint_prmPiece hunion
  rwa [iUnion_prmPiece, setIntegral_univ] at h

private theorem integrable_pieceSum [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    (hf : Measurable f) (hf1 : Integrable f m) (hf2 : MemLp f 2 m) :
    Integrable (pieceSum K X f k) μ :=
  ((memLp_two_iff_integrable_sq
    (measurable_pieceSum (hd.measurable_count k) (hd.measurable_point k) hf).aestronglyMeasurable).mpr
      (integrable_sq_pieceSum hd hf hf1.integrableOn hf2.integrable_sq.integrableOn)).integrable
    one_le_two

/-- The compensated piece sum is measurable. -/

private theorem integral_norm_compensatedPieceSum_le [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hf : Measurable f) (hf1 : Integrable f m)
    (hf2 : MemLp f 2 m) :
    ∫ ω, ‖compensatedPieceSum K X f m k ω‖ ∂μ ≤ 2 * ∫ x in prmPiece m k, ‖f x‖ ∂m := by
  set C := ∫ x in prmPiece m k, f x ∂m with hC
  have hSnInt : Integrable (pieceSum K X (fun x => ‖f x‖) k) μ :=
    integrable_pieceSum (k := k) hd hf.norm hf1.norm hf2.norm
  have hcompInt : Integrable (compensatedPieceSum K X f m k) μ :=
    integrable_compensatedPieceSum (k := k) hd hf hf1 hf2
  have hle : ∀ ω, ‖compensatedPieceSum K X f m k ω‖ ≤ pieceSum K X (fun x => ‖f x‖) k ω + ‖C‖ := by
    intro ω
    have h1 : ‖compensatedPieceSum K X f m k ω‖ ≤ ‖pieceSum K X f k ω‖ + ‖C‖ := by
      simp only [compensatedPieceSum]; exact norm_sub_le _ _
    have h2 : ‖pieceSum K X f k ω‖ ≤ pieceSum K X (fun x => ‖f x‖) k ω := by
      simp only [pieceSum]
      exact norm_sum_le _ _
    linarith
  calc ∫ ω, ‖compensatedPieceSum K X f m k ω‖ ∂μ
      ≤ ∫ ω, (pieceSum K X (fun x => ‖f x‖) k ω + ‖C‖) ∂μ :=
        integral_mono hcompInt.norm (hSnInt.add (integrable_const _)) hle
    _ = (∫ ω, pieceSum K X (fun x => ‖f x‖) k ω ∂μ) + ‖C‖ := by
        rw [integral_add hSnInt (integrable_const _), integral_const, probReal_univ, one_smul]
    _ ≤ 2 * ∫ x in prmPiece m k, ‖f x‖ ∂m := by
        rw [integral_pieceSum hd hf.norm hf1.norm.integrableOn]
        have hCnorm : ‖C‖ ≤ ∫ x in prmPiece m k, ‖f x‖ ∂m := by
          rw [hC]; exact norm_integral_le_integral_norm _
        linarith

private theorem tsum_lintegral_enorm_compensatedPieceSum_ne_top [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hf : Measurable f) (hf1 : Integrable f m)
    (hf2 : MemLp f 2 m) :
    ∑' k, ∫⁻ ω, ‖compensatedPieceSum K X f m k ω‖ₑ ∂μ ≠ ⊤ := by
  have hbound : ∀ k, ∫⁻ ω, ‖compensatedPieceSum K X f m k ω‖ₑ ∂μ
      ≤ ENNReal.ofReal (2 * ∫ x in prmPiece m k, ‖f x‖ ∂m) := by
    intro k
    rw [← ofReal_integral_norm_eq_lintegral_enorm (integrable_compensatedPieceSum hd hf hf1 hf2)]
    exact ENNReal.ofReal_le_ofReal (integral_norm_compensatedPieceSum_le hd hf hf1 hf2)
  have hsum : Summable (fun k => 2 * ∫ x in prmPiece m k, ‖f x‖ ∂m) :=
    ((hasSum_setIntegral_prmPiece hf1.norm).mul_left 2).summable
  exact ne_top_of_le_ne_top hsum.tsum_ofReal_ne_top (ENNReal.tsum_le_tsum hbound)

theorem integral_compensatedPoissonSum [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    (hf : Measurable f) (hf1 : Integrable f m) (hf2 : MemLp f 2 m) :
    ∫ ω, compensatedPoissonSum K X f m ω ∂μ = 0 := by
  simp only [compensatedPoissonSum]
  rw [integral_tsum (fun k => (measurable_compensatedPieceSum hd hf).aestronglyMeasurable)
    (tsum_lintegral_enorm_compensatedPieceSum_ne_top hd hf hf1 hf2)]
  simp [integral_compensatedPieceSum hd hf hf1 hf2]
private theorem tendsto_integral_of_tendsto_Lp2 [IsProbabilityMeasure μ]
    {gn : ℕ → Lp ℝ 2 μ} {g : Lp ℝ 2 μ} (h : Tendsto gn atTop (𝓝 g)) :
    Tendsto (fun n => ∫ ω, gn n ω ∂μ) atTop (𝓝 (∫ ω, g ω ∂μ)) := by
  refine tendsto_iff_dist_tendsto_zero.mpr
    (squeeze_zero (g := fun n => dist (gn n) g) (fun n => dist_nonneg) (fun n => ?_) ?_)
  · set H : Lp ℝ 2 μ := gn n - g with hH
    have hint_gn : Integrable (⇑(gn n)) μ := (Lp.memLp (gn n)).integrable (by norm_num)
    have hint_g : Integrable (⇑g) μ := (Lp.memLp g).integrable (by norm_num)
    have key : (∫ ω, gn n ω ∂μ) - ∫ ω, g ω ∂μ = ∫ ω, H ω ∂μ := by
      rw [hH, integral_congr_ae (Lp.coeFn_sub (gn n) g)]
      simp only [Pi.sub_apply]
      rw [integral_sub hint_gn hint_g]
    rw [Real.dist_eq, key]
    calc |∫ ω, H ω ∂μ|
        = ‖∫ ω, H ω ∂μ‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ ω, ‖H ω‖ ∂μ := norm_integral_le_integral_norm _
      _ = (eLpNorm H 1 μ).toReal := by
            rw [integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable H),
              ← eLpNorm_one_eq_lintegral_enorm]
      _ ≤ (eLpNorm H 2 μ).toReal :=
            ENNReal.toReal_mono (Lp.eLpNorm_ne_top H)
              (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) (Lp.aestronglyMeasurable H))
      _ = ‖H‖ := (Lp.norm_def H).symm
      _ = dist (gn n) g := by rw [hH, ← dist_eq_norm]
  · have hdist := h.dist (tendsto_const_nhds (x := g))
    simpa using hdist
private theorem eLpNorm_two_toReal_eq_sqrt {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {h : α → ℝ} (hh : MemLp h 2 ν) :
    (eLpNorm h 2 ν).toReal = Real.sqrt (∫ a, (h a) ^ 2 ∂ν) := by
  rw [hh.eLpNorm_eq_integral_rpow_norm two_ne_zero (by norm_num),
    ENNReal.toReal_ofReal (by positivity)]
  have he : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [he]
  have hint : (∫ a, ‖h a‖ ^ (2 : ℝ) ∂ν) = ∫ a, (h a) ^ 2 ∂ν := by
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [hint, Real.sqrt_eq_rpow, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]

/-- The `L²(μ)` element attached to a measurable `L¹ ∩ L²` test function by the compensated Poisson
sum. -/
private noncomputable def compensatedPoissonToLp [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hf : Measurable f) (hf1 : Integrable f m)
    (hf2 : MemLp f 2 m) : Lp ℝ 2 μ :=
  (memLp_two_compensatedPoissonSum hd hf hf1 hf2).toLp (compensatedPoissonSum K X f m)

private theorem coeFn_compensatedPoissonToLp [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hf : Measurable f) (hf1 : Integrable f m)
    (hf2 : MemLp f 2 m) :
    ⇑(compensatedPoissonToLp hd hf hf1 hf2) =ᵐ[μ] compensatedPoissonSum K X f m :=
  MemLp.coeFn_toLp _

/-- The compensated Poisson map is an isometry from `L¹ ∩ L²` into `L²(μ)`. -/
private theorem norm_compensatedPoissonToLp [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hf : Measurable f) (hf1 : Integrable f m)
    (hf2 : MemLp f 2 m) :
    ‖compensatedPoissonToLp hd hf hf1 hf2‖ = (eLpNorm f 2 m).toReal := by
  unfold compensatedPoissonToLp
  rw [Lp.norm_toLp, eLpNorm_two_toReal_eq_sqrt (memLp_two_compensatedPoissonSum hd hf hf1 hf2),
    eLpNorm_two_toReal_eq_sqrt hf2, integral_sq_compensatedPoissonSum hd hf hf1 hf2]

/-- The distance between two compensated Poisson images is the `L²(m)`-distance of the test
functions (the isometry, in `dist` form). -/
private theorem dist_compensatedPoissonToLp [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hf : Measurable f) (hf1 : Integrable f m)
    (hf2 : MemLp f 2 m) (hg : Measurable g) (hg1 : Integrable g m) (hg2 : MemLp g 2 m) :
    dist (compensatedPoissonToLp hd hf hf1 hf2) (compensatedPoissonToLp hd hg hg1 hg2)
      = (eLpNorm (fun x => f x - g x) 2 m).toReal := by
  have hmemf := memLp_two_compensatedPoissonSum hd hf hf1 hf2
  have hmemg := memLp_two_compensatedPoissonSum hd hg hg1 hg2
  have hsub : ∀ᵐ ω ∂μ, (compensatedPoissonSum K X f m - compensatedPoissonSum K X g m) ω
      = compensatedPoissonSum K X (fun x => f x - g x) m ω := by
    filter_upwards [compensatedPoissonSum_sub hd hf hf1 hf2 hg hg1 hg2] with ω hω
    simpa [Pi.sub_apply] using hω.symm
  -- The `.sub` combinators yield the `f - g` (`Pi.sub`) shape, but the sum lemmas above
  -- carry the `fun x => f x - g x` shape; pin the fun-form so the rewrites line up.
  have hfg : Measurable (fun x => f x - g x) := hf.sub hg
  have hfg1 : Integrable (fun x => f x - g x) m := hf1.sub hg1
  have hfg2 : MemLp (fun x => f x - g x) 2 m := hf2.sub hg2
  rw [dist_eq_norm]
  unfold compensatedPoissonToLp
  rw [← MemLp.toLp_sub, Lp.norm_toLp, eLpNorm_congr_ae hsub,
    eLpNorm_two_toReal_eq_sqrt (memLp_two_compensatedPoissonSum hd hfg hfg1 hfg2),
    integral_sq_compensatedPoissonSum hd hfg hfg1 hfg2]
  exact (eLpNorm_two_toReal_eq_sqrt hfg2).symm

/-! ### Simple-function approximation and the density extension -/

omit [SigmaFinite m] [Nonempty E] in
/-- A simple-function approximation of `f ∈ L²(m)` accurate to `1 / (n + 1)`, extracted from
`MemLp.exists_simpleFunc_eLpNorm_sub_lt`. -/
private theorem exists_approxSimple (f : Lp ℝ 2 m) (n : ℕ) :
    ∃ h : SimpleFunc E ℝ, eLpNorm (⇑f - ⇑h) 2 m < ENNReal.ofReal (1 / (n + 1)) ∧ MemLp h 2 m :=
  (Lp.memLp f).exists_simpleFunc_eLpNorm_sub_lt (by norm_num)
    (ENNReal.ofReal_pos.mpr (by positivity)).ne'

private noncomputable def approxSimple (f : Lp ℝ 2 m) (n : ℕ) : SimpleFunc E ℝ :=
  (exists_approxSimple f n).choose

omit [SigmaFinite m] [Nonempty E] in
private theorem approxSimple_eLpNorm_lt (f : Lp ℝ 2 m) (n : ℕ) :
    eLpNorm (⇑f - ⇑(approxSimple f n)) 2 m < ENNReal.ofReal (1 / (n + 1)) :=
  (exists_approxSimple f n).choose_spec.1

omit [SigmaFinite m] [Nonempty E] in
private theorem approxSimple_memLp (f : Lp ℝ 2 m) (n : ℕ) : MemLp (approxSimple f n) 2 m :=
  (exists_approxSimple f n).choose_spec.2

omit [SigmaFinite m] [Nonempty E] in
private theorem approxSimple_measurable (f : Lp ℝ 2 m) (n : ℕ) :
    Measurable (⇑(approxSimple f n)) :=
  (approxSimple f n).measurable

omit [SigmaFinite m] [Nonempty E] in
private theorem approxSimple_integrable (f : Lp ℝ 2 m) (n : ℕ) :
    Integrable (⇑(approxSimple f n)) m :=
  (SimpleFunc.memLp_iff_integrable two_ne_zero (by norm_num)).mp (approxSimple_memLp f n)

omit [SigmaFinite m] [Nonempty E] in
private theorem approxSimple_eLpNorm_tendsto (f : Lp ℝ 2 m) :
    Tendsto (fun n => eLpNorm (⇑f - ⇑(approxSimple f n)) 2 m) atTop (𝓝 0) := by
  have hub : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / (n + 1))) atTop (𝓝 0) := by
    have hr : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp hr
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hub
    (Eventually.of_forall fun n => zero_le) (Eventually.of_forall fun n => ?_)
  exact (approxSimple_eLpNorm_lt f n).le

omit [SigmaFinite m] [Nonempty E] in
/-- The `L²(m)`-image of the approximation converges to `f`. -/
private theorem tendsto_toLp_approxSimple (f : Lp ℝ 2 m) :
    Tendsto (fun n => (approxSimple_memLp f n).toLp (⇑(approxSimple f n))) atTop (𝓝 f) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have heq : ∀ n, ‖(approxSimple_memLp f n).toLp (⇑(approxSimple f n)) - f‖
      = (eLpNorm (⇑f - ⇑(approxSimple f n)) 2 m).toReal := by
    intro n
    rw [Lp.norm_def]
    congr 1
    rw [eLpNorm_sub_comm (⇑f) (⇑(approxSimple f n))]
    refine eLpNorm_congr_ae ?_
    filter_upwards [Lp.coeFn_sub ((approxSimple_memLp f n).toLp (⇑(approxSimple f n))) f,
      MemLp.coeFn_toLp (approxSimple_memLp f n)] with x h1 h2
    rw [h1]; simp only [Pi.sub_apply]; rw [h2]
  simp_rw [heq]
  simpa [Function.comp_def] using (ENNReal.tendsto_toReal (by simp)).comp (approxSimple_eLpNorm_tendsto f)

/-- The compensated images of the approximation form a Cauchy sequence in `L²(μ)`. -/
private theorem cauchySeq_compApproxSeq [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (f : Lp ℝ 2 m) :
    CauchySeq (fun n => compensatedPoissonToLp hd (approxSimple_measurable f n)
      (approxSimple_integrable f n) (approxSimple_memLp f n)) := by
  have hb : CauchySeq (fun n => (approxSimple_memLp f n).toLp (⇑(approxSimple f n))) :=
    (tendsto_toLp_approxSimple f).cauchySeq
  have hdist : ∀ n k, dist (compensatedPoissonToLp hd (approxSimple_measurable f n)
        (approxSimple_integrable f n) (approxSimple_memLp f n))
        (compensatedPoissonToLp hd (approxSimple_measurable f k)
        (approxSimple_integrable f k) (approxSimple_memLp f k))
      = dist ((approxSimple_memLp f n).toLp (⇑(approxSimple f n)))
        ((approxSimple_memLp f k).toLp (⇑(approxSimple f k))) := by
    intro n k
    rw [dist_compensatedPoissonToLp, dist_eq_norm, ← MemLp.toLp_sub, Lp.norm_toLp]
    rfl
  rw [Metric.cauchySeq_iff] at hb ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hb ε hε
  exact ⟨N, fun n hn k hk => (hdist n k).symm ▸ hN n hn k hk⟩

/-- The **compensated Poisson integral** as a map `L²(m) → L²(μ)`: the `L²(μ)`-limit of the
compensated sums of a simple-function approximation of `f`.  It is an isometry
(`eLpNorm_compensatedPoissonIntegral`) and agrees a.e. with the explicit pathwise sum on `L¹ ∩ L²`
(`compensatedPoissonIntegral_eq_sum`). -/

private theorem compApproxSeq_tendsto [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (f : Lp ℝ 2 m) :
    Tendsto (fun n => compensatedPoissonToLp hd (approxSimple_measurable f n)
      (approxSimple_integrable f n) (approxSimple_memLp f n)) atTop
      (𝓝 (compensatedPoissonIntegral hd f)) :=
  (cauchySeq_tendsto_of_complete (cauchySeq_compApproxSeq hd f)).choose_spec

end ProbabilityTheory
open ProbabilityTheory
variable {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω]
  {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
  {m : Measure E} [SigmaFinite m] [Nonempty E] {μ : Measure Ω}
theorem solution [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (f : Lp ℝ 2 m) :
    ∫ ω, compensatedPoissonIntegral hd f ω ∂μ = 0 := by
  have htend := tendsto_integral_of_tendsto_Lp2 (compApproxSeq_tendsto hd f)
  have hzero : ∀ n, ∫ ω, compensatedPoissonToLp hd (approxSimple_measurable f n)
      (approxSimple_integrable f n) (approxSimple_memLp f n) ω ∂μ = 0 := by
    intro n
    rw [integral_congr_ae (coeFn_compensatedPoissonToLp hd _ _ _)]
    exact integral_compensatedPoissonSum hd (approxSimple_measurable f n)
      (approxSimple_integrable f n) (approxSimple_memLp f n)
  simp only [hzero] at htend
  exact tendsto_nhds_unique htend tendsto_const_nhds
