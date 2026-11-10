-- Prove2me | solution 1 for ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat29_psi_algebra
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T21:44:02.138859+00:00
-- url     : https://prove2.me/submissions/57030823-a797-4e1d-8026-5dd9b0ad6945

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_ProbabilityTheory_integrable_levyCompensatedIntegrand
import Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat30_sq_ball_integrable
import Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat30_compensated_integral_split
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder
namespace ProbabilityTheory.ConvolutionSemigroup
@[simp] private lemma mem_smallSet {x : ℝ} : x ∈ smallSet ↔ |x| < 1 := Iff.rfl
@[simp] lemma mem_largeSet {x : ℝ} {ε : ℝ} : x ∈ largeSet ε ↔ ε ≤ |x| := Iff.rfl
lemma measurableSet_smallSet : MeasurableSet smallSet := (isOpen_Iio.preimage continuous_abs).measurableSet
lemma measurableSet_largeSet (ε : ℝ) : MeasurableSet (largeSet ε) := (isClosed_Ici.preimage continuous_abs).measurableSet
lemma smallSet_eq_compl_largeSet : smallSet = (largeSet 1)ᶜ := by
  ext x; simp [smallSet, largeSet, not_le]
private lemma integrableOn_of_bounded_of_measure_lt_top {s : Set ℝ} {μ : Measure ℝ} (hs : μ s < ⊤) {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} (hf_cont : Continuous f) {M : ℝ} (hf_bnd : ∀ x, ‖f x‖ ≤ M) :
    IntegrableOn f s μ := by
  haveI : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.mpr hs.ne
  exact Integrable.mono' (integrable_const M) hf_cont.aestronglyMeasurable
    (Filter.Eventually.of_forall hf_bnd)
end ProbabilityTheory.ConvolutionSemigroup
open ProbabilityTheory.ConvolutionSemigroup
theorem solution {r : ℝ} (hr : r ∈ Set.Ioc (1/2 : ℝ) 1) (ξ : ℝ)
    {ν : Measure ℝ} (hν : IsLevyMeasure ν) (b_r : ℝ) (σ_sq_r : ℝ≥0) :
    (↑b_r * ↑ξ * I
      + (-(↑(σ_sq_r : ℝ) * ↑ξ ^ 2 / 2)
          + ∫ x in {x | |x| < r},
              (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) ∂ν))
      + ∫ x in largeSet r, (exp ((↑x : ℂ) * ↑ξ * I) - 1) ∂ν =
    ↑(b_r + ∫ x in {x | r ≤ |x| ∧ |x| < 1}, x ∂ν) * ↑ξ * I
      - ↑((σ_sq_r : ℝ) - ∫ x in {x | |x| < r}, x ^ 2 ∂ν) * ↑ξ ^ 2 / 2
      + ∫ x, levyCompensatedIntegrand ξ x ∂ν := by
  have hr_pos : (0 : ℝ) < r := by linarith [hr.1]
  have hr1 : r ≤ 1 := hr.2
  set Bball : Set ℝ := {x | |x| < r} with hBball_def
  set Bband : Set ℝ := {x | r ≤ |x| ∧ |x| < 1} with hBband_def
  have hmeas_ball : MeasurableSet Bball := measurableSet_lt continuous_abs.measurable measurable_const
  have hmeas_band : MeasurableSet Bband := (measurableSet_le measurable_const continuous_abs.measurable).inter
    (measurableSet_lt continuous_abs.measurable measurable_const)
  have hmeas_ge1 : MeasurableSet (largeSet 1) := measurableSet_largeSet 1
  have hg_cont : Continuous (fun x : ℝ => exp ((↑x : ℂ) * ↑ξ * I) - 1) :=
    ((Complex.continuous_exp.comp ((Complex.continuous_ofReal.mul continuous_const).mul continuous_const)).sub continuous_const)
  have hg_bnd : ∀ x : ℝ, ‖exp ((↑x : ℂ) * ↑ξ * I) - 1‖ ≤ 2 := fun x => by
    rw [show ((↑x : ℂ) * ↑ξ * I) = ((↑(x * ξ) : ℂ)) * I from by push_cast; ring]
    calc ‖exp ((↑(x * ξ) : ℂ) * I) - 1‖
        ≤ ‖exp ((↑(x * ξ) : ℂ) * I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [Complex.norm_exp_ofReal_mul_I, norm_one]; norm_num
  have hν_band_lt : ν Bband < ⊤ :=
    lt_of_le_of_lt (measure_mono (fun x hx => hx.1)) (hν.measure_setOf_abs_ge_lt_top hr_pos)
  have hν_ge1_lt : ν (largeSet 1) < ⊤ := hν.measure_setOf_abs_ge_lt_top one_pos
  have hexp_int : ∀ s : Set ℝ, ν s < ⊤ → IntegrableOn (fun x : ℝ => exp ((↑x : ℂ) * ↑ξ * I) - 1) s ν :=
    fun s hs => integrableOn_of_bounded_of_measure_lt_top hs hg_cont hg_bnd
  have hxi_intOn : ∀ s : Set ℝ, MeasurableSet s → s ⊆ {x : ℝ | |x| < 1} → ν s < ⊤ → IntegrableOn (fun x : ℝ => (↑x : ℂ) * ↑ξ * I) s ν := by
    intro s hs hsub hfin
    haveI : IsFiniteMeasure (ν.restrict s) := isFiniteMeasure_restrict.mpr hfin.ne
    refine (integrable_const (|ξ|)).mono' ?_ ?_
    · exact ((Complex.measurable_ofReal.mul measurable_const).mul
        measurable_const).aestronglyMeasurable
    · refine (ae_restrict_iff' hs).mpr (Filter.Eventually.of_forall (fun x hx => ?_))
      have hx1 : |x| < 1 := hsub hx
      have hnorm : ‖((↑x : ℂ) * ↑ξ * I)‖ = |x| * |ξ| := by
        rw [show ((↑x : ℂ) * ↑ξ * I) = ((↑(x * ξ) : ℂ)) * I from by push_cast; ring,
            norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      rw [hnorm]
      calc |x| * |ξ| ≤ 1 * |ξ| :=
            mul_le_mul_of_nonneg_right (le_of_lt hx1) (abs_nonneg _)
        _ = |ξ| := one_mul _
  set A : ℂ := ∫ x in Bball, (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I) ∂ν with hA_def
  set Bcpx : ℂ := ∫ x in Bband, (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I) ∂ν with hBcpx_def
  set Ctail : ℂ := ∫ x in largeSet 1, (exp ((↑x : ℂ) * ↑ξ * I) - 1) ∂ν with hCtail_def
  set Pball : ℝ := ∫ x in Bball, x ^ 2 ∂ν with hPball_def
  set Pbar : ℝ := ∫ x in Bband, x ∂ν with hPbar_def
  have hquad_ball : IntegrableOn (fun x : ℝ => ((↑x : ℂ) * ↑ξ) ^ 2 / 2) Bball ν := by
    have hrw : (fun x : ℝ => ((↑x : ℂ) * ↑ξ) ^ 2 / 2) =
        fun x : ℝ => (↑((x ^ 2 * (ξ ^ 2 / 2) : ℝ)) : ℂ) := by
      funext x; push_cast; ring
    rw [hrw]
    exact ((leanlevy_chat30_sq_ball_integrable hν r).mul_const (ξ ^ 2 / 2)).ofReal
  have hcomp_ball : IntegrableOn
      (fun x : ℝ => exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I) Bball ν := by
    refine ((integrable_levyCompensatedIntegrand hν ξ).integrableOn).congr ?_
    filter_upwards [ae_restrict_mem hmeas_ball] with x hx
    have hx1 : |x| < 1 := lt_of_lt_of_le hx hr1
    simp [levyCompensatedIntegrand, hx1]
  have h_id1 : (∫ x in Bball,
      (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) ∂ν)
      = A + (↑Pball : ℂ) * ↑ξ ^ 2 / 2 := by
    rw [integral_add hcomp_ball hquad_ball, hA_def]
    congr 1
    have hquad_eq : ∀ x : ℝ, ((↑x : ℂ) * ↑ξ) ^ 2 / 2 = (↑ξ ^ 2 / 2 : ℂ) * (↑(x ^ 2) : ℂ) := by
      intro x; push_cast; ring
    calc (∫ x in Bball, ((↑x : ℂ) * ↑ξ) ^ 2 / 2 ∂ν)
        = ∫ x in Bball, (↑ξ ^ 2 / 2 : ℂ) * (↑(x ^ 2) : ℂ) ∂ν :=
          setIntegral_congr_fun hmeas_ball (fun x _ => hquad_eq x)
      _ = (↑ξ ^ 2 / 2 : ℂ) * ∫ x in Bball, (↑(x ^ 2) : ℂ) ∂ν := integral_const_mul _ _
      _ = (↑ξ ^ 2 / 2 : ℂ) * (↑Pball : ℂ) := by
          rw [hPball_def]; congr 1; exact integral_complex_ofReal
      _ = (↑Pball : ℂ) * ↑ξ ^ 2 / 2 := by ring
  have h_id2 : (∫ x in largeSet r, (exp ((↑x : ℂ) * ↑ξ * I) - 1) ∂ν)
      = (∫ x in Bband, (exp ((↑x : ℂ) * ↑ξ * I) - 1) ∂ν) + Ctail := by
    have h_disj : Disjoint Bband (largeSet 1) := by
      rw [Set.disjoint_left]
      intro x hx hx'
      exact absurd (mem_largeSet.mp hx') (not_le.mpr hx.2)
    have h_union : largeSet r = Bband ∪ largeSet 1 := by
      ext x
      simp only [largeSet, hBband_def, Set.mem_setOf_eq, Set.mem_union]
      constructor
      · intro hx
        rcases lt_or_ge (|x|) 1 with h | h
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr h
      · rintro (⟨h, _⟩ | h)
        · exact h
        · exact le_trans hr1 h
    rw [hCtail_def, h_union,
      setIntegral_union h_disj hmeas_ge1 (hexp_int Bband hν_band_lt)
        (hexp_int (largeSet 1) hν_ge1_lt)]
  have hband_sub : Bband ⊆ {x : ℝ | |x| < 1} := fun x hx => hx.2
  have hxi_band : IntegrableOn (fun x : ℝ => (↑x : ℂ) * ↑ξ * I) Bband ν :=
    hxi_intOn Bband hmeas_band hband_sub hν_band_lt
  have hcomp_band : IntegrableOn
      (fun x : ℝ => exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I) Bband ν :=
    (hexp_int Bband hν_band_lt).sub hxi_band
  have h_id3 : (∫ x in Bband, (exp ((↑x : ℂ) * ↑ξ * I) - 1) ∂ν)
      = Bcpx + (↑Pbar : ℂ) * ↑ξ * I := by
    have hsplit : (∫ x in Bband, (exp ((↑x : ℂ) * ↑ξ * I) - 1) ∂ν)
        = Bcpx + ∫ x in Bband, ((↑x : ℂ) * ↑ξ * I) ∂ν := by
      rw [hBcpx_def, ← integral_add hcomp_band hxi_band]
      exact setIntegral_congr_fun hmeas_band (fun x _ => by ring)
    rw [hsplit]
    congr 1
    calc (∫ x in Bband, ((↑x : ℂ) * ↑ξ * I) ∂ν)
        = ∫ x in Bband, ((↑ξ * I : ℂ) * (↑x : ℂ)) ∂ν :=
          setIntegral_congr_fun hmeas_band (fun x _ => by ring)
      _ = (↑ξ * I : ℂ) * ∫ x in Bband, (↑x : ℂ) ∂ν := integral_const_mul _ _
      _ = (↑ξ * I : ℂ) * (↑Pbar : ℂ) := by rw [hPbar_def]; congr 1; exact integral_complex_ofReal
      _ = (↑Pbar : ℂ) * ↑ξ * I := by ring
  have h_id4 : (∫ x, levyCompensatedIntegrand ξ x ∂ν) = A + Bcpx + Ctail := by
    simpa [hA_def, hBcpx_def, hCtail_def, hBball_def, hBband_def] using
      (leanlevy_chat30_compensated_integral_split hr ξ hν)
  rw [h_id1, h_id2, h_id3, h_id4]
  push_cast
  ring
