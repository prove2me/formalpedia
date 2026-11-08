-- Prove2me | solution 1 for QiFixedDesign.Concentration.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T02:19:34.824749+00:00
-- url     : https://prove2.me/submissions/4eae4cd1-eb49-4f6b-ae99-4aee27bedb67

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance

open MeasureTheory Matrix Filter Topology
open scoped ENNReal

namespace QiFixedDesign.Concentration.Aux_QF

/-- clamp to `[-M, M]` -/
noncomputable def clamp (M u : ℝ) : ℝ := max (min u M) (-M)

theorem clamp_lip (M a b : ℝ) : |clamp M a - clamp M b| ≤ |a - b| := by
  unfold clamp
  exact (abs_max_sub_max_le_abs _ _ _).trans (by
    have := abs_min_sub_min_le_max a M b M
    simp only [sub_self, abs_zero] at this
    exact this.trans (max_le le_rfl (abs_nonneg _)))

theorem clamp_of_le {M u : ℝ} (h : |u| ≤ M) : clamp M u = u := by
  unfold clamp
  rw [abs_le] at h
  rw [min_eq_left h.2, max_eq_left h.1]

theorem clamp_cont (M : ℝ) : Continuous (clamp M) := by
  unfold clamp; fun_prop

theorem clamp_bound {M : ℝ} (hM : 0 ≤ M) (u : ℝ) : |clamp M u| ≤ M := by
  unfold clamp
  rw [abs_le]
  constructor
  · exact le_max_right _ _
  · exact max_le (min_le_right _ _) (by linarith)

end QiFixedDesign.Concentration.Aux_QF

open QiFixedDesign.Concentration.Aux_QF in
theorem solution (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (t : ℝ) (hν : ν = μ.map (fun u => u + t)) :
    WassersteinDRO.Duality.wassersteinDistance 1 μ ν = ENNReal.ofReal |t| := by
  unfold WassersteinDRO.Duality.wassersteinDistance
  rw [div_one, ENNReal.rpow_one]
  have hmeas_shift : Measurable fun u : ℝ => u + t := measurable_id.add_const t
  apply le_antisymm
  · -- the shift coupling
    set π : Measure (ℝ × ℝ) := μ.map (fun u => (u, u + t)) with hπ
    have hmeasp : Measurable fun u : ℝ => (u, u + t) := measurable_id.prodMk hmeas_shift
    refine iInf₂_le_of_le π ⟨?_, ?_⟩ ?_
    · rw [hπ, Measure.map_map measurable_fst hmeasp]
      exact Measure.map_id
    · rw [hπ, Measure.map_map measurable_snd hmeasp, hν]
      rfl
    · have hmf : Measurable fun x : ℝ × ℝ => ENNReal.ofReal (‖x.1 - x.2‖ ^ (1 : ℝ)) :=
        ENNReal.measurable_ofReal.comp ((measurable_fst.sub measurable_snd).norm.pow_const 1)
      rw [hπ, lintegral_map hmf hmeasp]
      have hc : ∀ u : ℝ, ENNReal.ofReal (‖(u, u + t).1 - (u, u + t).2‖ ^ (1 : ℝ)) =
          ENNReal.ofReal |t| := by
        intro u
        simp [Real.rpow_one, Real.norm_eq_abs]
      rw [lintegral_congr (fun u => hc u), lintegral_const, measure_univ, mul_one]
  · apply le_iInf₂
    rintro π ⟨h1, h2⟩
    haveI : IsProbabilityMeasure π := by
      constructor
      have h3 : (π.map Prod.fst) Set.univ = μ Set.univ := by rw [h1]
      rw [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ] at h3
      rw [h3]
      exact measure_univ
    simp only [Real.rpow_one, Real.norm_eq_abs]
    -- clamped test functions
    set h : ℝ → ℝ := fun M => ∫ u, (clamp M (u + t) - clamp M u) ∂μ with hh
    have hbound_meas : ∀ M : ℝ, ∀ g : ℝ × ℝ → ℝ, Continuous g →
        (∀ w, |g w| ≤ 2 * |M|) → Integrable g π := by
      intro M g hg hb
      exact Integrable.of_bound hg.aestronglyMeasurable (2 * |M|) (Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs]; exact hb w)
    have hkey : ∀ M : ℝ, 0 ≤ M → ∀ s : ℝ, s = 1 ∨ s = -1 →
        ENNReal.ofReal (s * h M) ≤ ∫⁻ w, ENNReal.ofReal |w.1 - w.2| ∂π := by
      intro M hM s hs
      set g : ℝ × ℝ → ℝ := fun w => s * (clamp M w.2 - clamp M w.1) with hg
      have hgc : Continuous g := by
        rw [hg]; exact continuous_const.mul
          (((clamp_cont M).comp continuous_snd).sub ((clamp_cont M).comp continuous_fst))
      have hgb : ∀ w, |g w| ≤ 2 * |M| := by
        intro w
        rw [hg]
        simp only
        rw [abs_mul]
        have hs1 : |s| = 1 := by rcases hs with rfl | rfl <;> simp
        rw [hs1, one_mul, abs_of_nonneg hM]
        have := abs_sub (clamp M w.2) (clamp M w.1)
        have := clamp_bound hM w.2
        have := clamp_bound hM w.1
        linarith
      have hgi : Integrable g π := hbound_meas M g hgc hgb
      have hint : ∫ w, g w ∂π = s * h M := by
        rw [hg, integral_const_mul, integral_sub]
        · rw [← integral_map measurable_snd.aemeasurable (clamp_cont M).aestronglyMeasurable,
            ← integral_map measurable_fst.aemeasurable (clamp_cont M).aestronglyMeasurable, h1, h2,
            hν, integral_map hmeas_shift.aemeasurable (clamp_cont M).aestronglyMeasurable, hh]
          simp only
          rw [integral_sub]
          · exact Integrable.of_bound ((clamp_cont M).comp (continuous_id.add continuous_const)).aestronglyMeasurable
              M (Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact clamp_bound hM _)
          · exact Integrable.of_bound (clamp_cont M).aestronglyMeasurable
              M (Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact clamp_bound hM _)
        · exact Integrable.of_bound ((clamp_cont M).comp continuous_snd).aestronglyMeasurable
            M (Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact clamp_bound hM _)
        · exact Integrable.of_bound ((clamp_cont M).comp continuous_fst).aestronglyMeasurable
            M (Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact clamp_bound hM _)
      have hgle : ∀ w, g w ≤ |w.1 - w.2| := by
        intro w
        rw [hg]
        simp only
        have hl := clamp_lip M w.2 w.1
        rw [abs_sub_comm w.2 w.1] at hl
        rcases hs with rfl | rfl
        · linarith [le_abs_self (clamp M w.2 - clamp M w.1)]
        · linarith [neg_abs_le (clamp M w.2 - clamp M w.1)]
      rw [← hint]
      have hmax : Integrable (fun w => max (g w) 0) π := hgi.sup (integrable_zero _ _ _)
      calc ENNReal.ofReal (∫ w, g w ∂π) ≤ ENNReal.ofReal (∫ w, max (g w) 0 ∂π) := by
            apply ENNReal.ofReal_le_ofReal
            exact integral_mono hgi hmax (fun w => le_max_left _ _)
        _ = ∫⁻ w, ENNReal.ofReal (max (g w) 0) ∂π :=
            ofReal_integral_eq_lintegral_ofReal hmax (Eventually.of_forall fun w => le_max_right _ _)
        _ ≤ ∫⁻ w, ENNReal.ofReal |w.1 - w.2| ∂π := by
            apply lintegral_mono
            intro w
            apply ENNReal.ofReal_le_ofReal
            exact max_le (hgle w) (abs_nonneg _)
    -- h M → t
    have hlim : Tendsto h atTop (𝓝 t) := by
      have := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := atTop)
        (F := fun M u => clamp M (u + t) - clamp M u) (f := fun _ => t) (fun _ => |t|)
        (Eventually.of_forall fun M =>
          (((clamp_cont M).comp (continuous_id.add continuous_const)).sub
            (clamp_cont M)).aestronglyMeasurable)
        (Eventually.of_forall fun M => Eventually.of_forall fun u => by
          rw [Real.norm_eq_abs]
          have := clamp_lip M (u + t) u
          simp only [add_sub_cancel_left] at this
          exact this)
        (integrable_const _)
        (Eventually.of_forall fun u => by
          apply tendsto_const_nhds.congr'
          filter_upwards [eventually_ge_atTop (|u| + |t|)] with M hM
          rw [clamp_of_le (by linarith [abs_add_le u t]), clamp_of_le (by linarith [abs_nonneg t])]
          ring)
      simpa [hh] using this
    have hlimabs : Tendsto (fun M => ENNReal.ofReal |h M|) atTop (𝓝 (ENNReal.ofReal |t|)) :=
      (ENNReal.continuous_ofReal.tendsto _).comp (hlim.abs)
    apply le_of_tendsto hlimabs
    filter_upwards [eventually_ge_atTop 0] with M hM
    rcases le_total 0 (h M) with hpos | hneg
    · rw [abs_of_nonneg hpos]
      have := hkey M hM 1 (Or.inl rfl)
      rwa [one_mul] at this
    · rw [abs_of_nonpos hneg]
      have := hkey M hM (-1) (Or.inr rfl)
      rwa [neg_one_mul] at this
