-- Prove2me | solution 1 for SalesRebate.NoIncreasing.Supplement.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:04:44.050229+00:00
-- url     : https://prove2.me/submissions/9aa58dfd-a128-4d55-b22e-e58917510052

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Definitions.Def_SalesRebate_NoIncreasing_Setting
import Definitions.Def_SalesRebate_NoIncreasing_Supplement_Problems

open SalesRebate
open SalesRebate.NoIncreasing
open SalesRebate.NoIncreasing.Supplement

open MeasureTheory ProbabilityTheory BlackScholesModel Filter Topology

theorem solution :
    (∀ (M : Model), M.Valid → ∀ p : ℝ, M.IsMarketPrice p →
      p / (Real.sqrt (2 * Real.pi) * M.σ) ≤ M.σε / M.σθ →
      (∃ rhat c, IsOptimalSC M p rhat c) ∧
        ∀ rhat c, IsOptimalSC M p rhat c → IsOptimal3 M p rhat c) ∧
    (∀ θ σ p : ℝ, 0 < σ → (∀ s ∈ Set.Ioo 0 σ, (famModel θ σ s).IsMarketPrice p) →
      Tendsto (fun s => optValueRC (famModel θ σ s) p / optValue3 (famModel θ σ s) p)
        (𝓝[>] 0) (𝓝 1)) := by
          have hdens : ∀ (θ a b x v : ℝ), 0 < a → 0 < b →
              gaussianPDFReal θ (a ^ 2).toNNReal v * gaussianPDFReal v (b ^ 2).toNNReal x =
                gaussianPDFReal θ (b ^ 2 + a ^ 2).toNNReal x *
                  gaussianPDFReal (a ^ 2 / (b ^ 2 + a ^ 2) * x + (1 - a ^ 2 / (b ^ 2 + a ^ 2)) * θ)
                    (b ^ 2 * a ^ 2 / (b ^ 2 + a ^ 2)).toNNReal v := by
            intro θ a b x v ha hb
            simp only [gaussianPDFReal_def, Real.coe_toNNReal _ (by positivity : (0:ℝ) ≤ a ^ 2),
              Real.coe_toNNReal _ (by positivity : (0:ℝ) ≤ b ^ 2),
              Real.coe_toNNReal _ (by positivity : (0:ℝ) ≤ b ^ 2 + a ^ 2),
              Real.coe_toNNReal _ (by positivity : (0:ℝ) ≤ b ^ 2 * a ^ 2 / (b ^ 2 + a ^ 2))]
            have hs : (√(2 * Real.pi * a ^ 2))⁻¹ * (√(2 * Real.pi * b ^ 2))⁻¹ =
                (√(2 * Real.pi * (b ^ 2 + a ^ 2)))⁻¹ * (√(2 * Real.pi * (b ^ 2 * a ^ 2 / (b ^ 2 + a ^ 2))))⁻¹ := by
              rw [← mul_inv, ← mul_inv, ← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
              congr 2; field_simp
            have he : -(v - θ) ^ 2 / (2 * a ^ 2) + -(x - v) ^ 2 / (2 * b ^ 2) =
                -(x - θ) ^ 2 / (2 * (b ^ 2 + a ^ 2)) +
                  -(v - (a ^ 2 / (b ^ 2 + a ^ 2) * x + (1 - a ^ 2 / (b ^ 2 + a ^ 2)) * θ)) ^ 2 /
                    (2 * (b ^ 2 * a ^ 2 / (b ^ 2 + a ^ 2))) := by
              field_simp; ring
            calc _ = ((√(2 * Real.pi * a ^ 2))⁻¹ * (√(2 * Real.pi * b ^ 2))⁻¹) *
                  Real.exp (-(v - θ) ^ 2 / (2 * a ^ 2) + -(x - v) ^ 2 / (2 * b ^ 2)) := by
                    rw [Real.exp_add]; ring
              _ = _ := by rw [hs, he, Real.exp_add]; ring
          refine ⟨?_, ?_⟩
          · intro M hM p hp hcond
            have hε := hM.σε_pos
            have hθ := hM.σθ_pos
            have hσ : 0 < M.σ := Real.sqrt_pos.2 (by positivity)
            have hpi : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
            have hspread : p ≤ spreadBound M := by
              unfold spreadBound
              rw [div_le_div_iff₀ (by positivity) hθ] at hcond
              rw [le_div_iff₀ hθ]
              nlinarith [mul_pos hpi hσ]
            have h3SC : ∀ r c, Feasible3 M p r c → FeasibleSC M p r c := by
              rintro r c ⟨hadm, h1, h2⟩
              refine ⟨hadm, fun v w => ?_, ?_⟩
              · have := (hadm.2 v).2; have := (hadm.2 w).1; linarith
              · have := h1 c le_rfl; have := h2 c le_rfl; linarith
            have hmono : ∀ r, IsAdmissibleReward p r → Monotone (fun x => x - p + M.condReward r x) := by
              intro r hadm x y hxy
              simp only
              have hp0 : 0 ≤ p := le_trans (hadm.2 0).1 (hadm.2 0).2
              set s2 : NNReal := M.σv2.toNNReal with hs2
              have hv2pos : 0 < M.σv2 := by unfold Model.σv2; positivity
              have hs2ne : s2 ≠ 0 := by simp [hs2, hv2pos]
              have hs2coe : (s2 : ℝ) = M.σv2 := Real.coe_toNNReal _ hv2pos.le
              set a := M.postMean x with ha
              set b := M.postMean y with hb
              have hτ : 0 ≤ M.tau := by unfold Model.tau; positivity
              have hab : b - a = M.tau * (y - x) := by simp only [a, b, Model.postMean]; ring
              have hh : 0 ≤ b - a := by rw [hab]; exact mul_nonneg hτ (by linarith)
              set c : ℝ := (Real.sqrt (2 * Real.pi * (s2:ℝ)))⁻¹ with hc
              have hrb : ∀ v, ‖r v‖ ≤ p := fun v => by
                rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hadm.2 v).1, (hadm.2 v).2]
              have hint : ∀ μ, Integrable (fun w => gaussianPDFReal μ s2 w * r w) := fun μ =>
                (integrable_gaussianPDFReal μ s2).mul_bdd hadm.1.aestronglyMeasurable
                  (Eventually.of_forall hrb)
              have hCR : ∀ μ, ∫ v, r v ∂(gaussianReal μ s2) = ∫ w, gaussianPDFReal μ s2 w * r w := fun μ => by
                rw [integral_gaussianReal_eq_integral_smul hs2ne]; simp [smul_eq_mul]
              have hdiff : M.condReward r y - M.condReward r x =
                  ∫ w, (gaussianPDFReal b s2 w - gaussianPDFReal a s2 w) * r w := by
                unfold Model.condReward Model.posterior
                rw [hCR, hCR, ← integral_sub (hint _) (hint _)]
                congr 1; ext w; ring
              set m := (a + b) / 2 with hm
              have hcmp : ∀ μ ν w : ℝ, (w - μ) ^ 2 ≤ (w - ν) ^ 2 →
                  gaussianPDFReal ν s2 w ≤ gaussianPDFReal μ s2 w := by
                intro μ ν w hw
                rw [gaussianPDFReal_def]
                simp only
                refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
                exact div_le_div_of_nonneg_right (neg_le_neg hw) (by positivity)
              have hpt : ∀ w, p * Set.indicator (Set.Iio m)
                  (fun w => gaussianPDFReal b s2 w - gaussianPDFReal a s2 w) w ≤
                  (gaussianPDFReal b s2 w - gaussianPDFReal a s2 w) * r w := by
                intro w
                have e : (w - b) ^ 2 - (w - a) ^ 2 = (b - a) * (a + b - 2 * w) := by ring
                by_cases hw : w < m
                · rw [Set.indicator_of_mem (show w ∈ Set.Iio m from hw)]
                  have h0 := mul_nonneg hh (show 0 ≤ a + b - 2 * w by rw [hm] at hw; linarith only [hw])
                  have := hcmp a b w (by linarith only [e, h0])
                  have := mul_le_mul_of_nonpos_left (hadm.2 w).2 (show gaussianPDFReal b s2 w - gaussianPDFReal a s2 w ≤ 0 by linarith only [this])
                  linarith only [this]
                · rw [Set.indicator_of_notMem (show w ∉ Set.Iio m from hw)]
                  have h0 := mul_nonneg hh (show 0 ≤ 2 * w - (a + b) by rw [hm] at hw; push Not at hw; linarith only [hw])
                  have := hcmp b a w (by linarith only [e, h0])
                  have := (hadm.2 w).1
                  simp only [mul_zero]
                  exact mul_nonneg (by linarith only [this, ‹gaussianPDFReal a s2 w ≤ gaussianPDFReal b s2 w›]) this
              have hdint : Integrable (fun w => gaussianPDFReal b s2 w - gaussianPDFReal a s2 w) :=
                (integrable_gaussianPDFReal b s2).sub (integrable_gaussianPDFReal a s2)
              have h1 : p * ∫ w, Set.indicator (Set.Iio m)
                  (fun w => gaussianPDFReal b s2 w - gaussianPDFReal a s2 w) w ≤
                  M.condReward r y - M.condReward r x := by
                rw [hdiff, ← integral_const_mul]
                refine integral_mono ((hdint.indicator measurableSet_Iio).const_mul p) ?_ hpt
                exact (hint b).sub (hint a) |>.congr (Eventually.of_forall fun w => by simp; ring)
              -- shift
              have hshift : ∫ w, Set.indicator (Set.Iio m) (gaussianPDFReal b s2) w =
                  ∫ w, Set.indicator (Set.Iio (m - (b - a))) (gaussianPDFReal a s2) w := by
                rw [← integral_sub_right_eq_self
                  (fun w => Set.indicator (Set.Iio m) (gaussianPDFReal b s2) w) (-(b - a))]
                congr 1; ext w
                by_cases hw : w < m - (b - a)
                · rw [Set.indicator_of_mem (show w ∈ Set.Iio (m - (b - a)) from hw),
                    Set.indicator_of_mem (show w - -(b - a) ∈ Set.Iio m by simp only [Set.mem_Iio]; linarith)]
                  simp only [gaussianPDFReal_def]; ring_nf
                · rw [Set.indicator_of_notMem (show w ∉ Set.Iio (m - (b - a)) from hw),
                    Set.indicator_of_notMem (show w - -(b - a) ∉ Set.Iio m by simp only [Set.mem_Iio]; push Not at hw ⊢; linarith)]
              have hfa_le : ∀ w, gaussianPDFReal a s2 w ≤ c := by
                intro w; rw [gaussianPDFReal_def]
                have : Real.exp (-(w - a) ^ 2 / (2 * (s2:ℝ))) ≤ 1 := by
                  rw [Real.exp_le_one_iff]; apply div_nonpos_of_nonpos_of_nonneg
                  · linarith only [sq_nonneg (w - a)]
                  · exact mul_nonneg zero_le_two s2.2
                exact mul_le_of_le_one_right (inv_nonneg.2 (Real.sqrt_nonneg _)) this
              have hia := integrable_gaussianPDFReal a s2
              have hib := integrable_gaussianPDFReal b s2
              have h2 : (∫ w, Set.indicator (Set.Iio m) (gaussianPDFReal a s2) w) -
                  ∫ w, Set.indicator (Set.Iio (m - (b - a))) (gaussianPDFReal a s2) w ≤ c * (b - a) := by
                rw [← integral_sub (hia.indicator measurableSet_Iio) (hia.indicator measurableSet_Iio)]
                have hconst : ∫ w, Set.indicator (Set.Ico (m - (b - a)) m) (fun _ => c) w = (b - a) * c := by
                  rw [integral_indicator_const _ measurableSet_Ico, Real.volume_real_Ico_of_le (by linarith)]
                  simp
                calc _ ≤ ∫ w, Set.indicator (Set.Ico (m - (b - a)) m) (fun _ => c) w := by
                      refine integral_mono ((hia.indicator measurableSet_Iio).sub
                        (hia.indicator measurableSet_Iio)) ?_ ?_
                      · exact (integrableOn_const (by simp [Real.volume_Ico])).integrable_indicator measurableSet_Ico
                      · intro w
                        simp only [Pi.sub_apply]
                        have h0 := gaussianPDFReal_nonneg a s2 w
                        have hc' := hfa_le w
                        by_cases hw1 : w < m - (b - a)
                        · rw [Set.indicator_of_mem (show w ∈ Set.Iio m by simp only [Set.mem_Iio]; linarith),
                            Set.indicator_of_mem (show w ∈ Set.Iio (m - (b - a)) from hw1)]
                          have : 0 ≤ Set.indicator (Set.Ico (m - (b - a)) m) (fun _ => c) w :=
                            Set.indicator_nonneg (fun _ _ => le_trans h0 hc') w
                          simpa using this
                        · rw [Set.indicator_of_notMem (show w ∉ Set.Iio (m - (b - a)) from hw1)]
                          by_cases hw2 : w < m
                          · rw [Set.indicator_of_mem (show w ∈ Set.Iio m from hw2),
                              Set.indicator_of_mem (show w ∈ Set.Ico (m - (b - a)) m from
                                ⟨by push Not at hw1; exact hw1, hw2⟩)]
                            simpa using hc'
                          · rw [Set.indicator_of_notMem (show w ∉ Set.Iio m from hw2),
                              Set.indicator_of_notMem (show w ∉ Set.Ico (m - (b - a)) m from
                                fun h => hw2 h.2)]
                            simp
                  _ = c * (b - a) := by rw [hconst]; ring
              have h3 : ∫ w, Set.indicator (Set.Iio m)
                  (fun w => gaussianPDFReal b s2 w - gaussianPDFReal a s2 w) w =
                  (∫ w, Set.indicator (Set.Iio m) (gaussianPDFReal b s2) w) -
                    ∫ w, Set.indicator (Set.Iio m) (gaussianPDFReal a s2) w := by
                rw [← integral_sub (hib.indicator measurableSet_Iio) (hia.indicator measurableSet_Iio)]
                congr 1; ext w; rw [Set.indicator_sub]
              -- constant algebra
              have hσ : 0 < M.σ := Real.sqrt_pos.2 (by positivity)
              have hσsq : M.σ ^ 2 = M.σε ^ 2 + M.σθ ^ 2 := Real.sq_sqrt (by positivity)
              have hpi : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
              have hpisq : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi := Real.sq_sqrt (by positivity)
              have hK : Real.sqrt (2 * Real.pi * (s2:ℝ)) = Real.sqrt (2 * Real.pi) * M.σε * M.σθ / M.σ := by
                rw [hs2coe]
                have : 2 * Real.pi * M.σv2 = (Real.sqrt (2 * Real.pi) * M.σε * M.σθ / M.σ) ^ 2 := by
                  unfold Model.σv2
                  rw [div_pow, ← hσsq]
                  field_simp
                  rw [hpisq]
                rw [this, Real.sqrt_sq (by positivity)]
              have hkey : spreadBound M * M.tau * c = 1 := by
                rw [hc, hK]
                unfold spreadBound Model.tau
                rw [← hσsq]
                field_simp
              have hpc : p * (c * (b - a)) ≤ y - x := by
                have hc0 : 0 ≤ c := by positivity
                calc p * (c * (b - a)) ≤ spreadBound M * (c * (b - a)) :=
                      mul_le_mul_of_nonneg_right hspread (mul_nonneg hc0 hh)
                  _ = (spreadBound M * M.tau * c) * (y - x) := by rw [hab]; ring
                  _ = y - x := by rw [hkey]; ring
              rw [h3, hshift] at h1
              have := mul_le_mul_of_nonneg_left h2 hp0
              linarith only [this, h1, hpc]
            have hSC3 : ∀ r c, FeasibleSC M p r c → Feasible3 M p r c := by
              rintro r c ⟨hadm, -, heq⟩
              refine ⟨hadm, fun x hx => ?_, fun x hx => ?_⟩
              · have := hmono r hadm hx; simp only at this; linarith
              · have := hmono r hadm hx; simp only at this; linarith
            refine ⟨?_, ?_⟩
            · clear h3SC hmono hSC3 hcond hσ hpi
              have hε := hM.σε_pos
              have hθ := hM.σθ_pos
              set sv : ℝ := Real.sqrt M.σv2 with hsv
              have hv2pos : 0 < M.σv2 := by unfold Model.σv2; positivity
              have hsvpos : 0 < sv := Real.sqrt_pos.2 hv2pos
              have hsq : M.σv2 = sv ^ 2 := (Real.sq_sqrt hv2pos.le).symm
              set rstar : ℝ → ℝ → ℝ := fun w => Set.indicator (Set.Iic w) (fun _ => p) with hrstar
              set cu : ℝ → ℝ := fun u => p * (1 - stdNormalCDF u) with hcu
              set wu : ℝ → ℝ := fun u => M.postMean (cu u) + sv * u with hwu
              set P : ℝ → ℝ := fun u => M.expectedProfit p (rstar (wu u)) (cu u) with hP
              set P0 : ℝ := M.expectedProfit p (fun _ => 0) p with hP0
              have hΦreal : ∀ t, stdNormalCDF t = (gaussianReal 0 1).real (Set.Iic t) := by
                intro t
                rw [measureReal_def, gaussianReal_apply_eq_integral _ one_ne_zero, ENNReal.toReal_ofReal
                  (setIntegral_nonneg measurableSet_Iic fun x _ => gaussianPDFReal_nonneg _ _ _)]
                unfold stdNormalCDF
                rw [← integral_const_mul]
                refine setIntegral_congr_fun measurableSet_Iic fun z _ => ?_
                simp [gaussianPDFReal_def]
              have hΦcdf : ∀ t, stdNormalCDF t = cdf (gaussianReal 0 1) t := fun t => by
                rw [hΦreal, cdf_eq_real]
              have hΦmono : Monotone stdNormalCDF := fun a b h => by
                rw [hΦcdf, hΦcdf]; exact monotone_cdf _ h
              have hΦ01 : ∀ t, 0 ≤ stdNormalCDF t ∧ stdNormalCDF t ≤ 1 := fun t => by
                rw [hΦcdf]; exact ⟨cdf_nonneg _ _, cdf_le_one _ _⟩
              have hΦtop : Tendsto stdNormalCDF atTop (𝓝 1) := by
                simp only [funext hΦcdf]; exact tendsto_cdf_atTop _
              have hΦbot : Tendsto stdNormalCDF atBot (𝓝 0) := by
                simp only [funext hΦcdf]; exact tendsto_cdf_atBot _
              have hΦcont : Continuous stdNormalCDF := by
                have hI : Integrable (fun z : ℝ => Real.exp (-z ^ 2 / 2)) := by
                  have := integrable_exp_neg_mul_sq (b := (1/2 : ℝ)) (by norm_num)
                  refine this.congr (Eventually.of_forall fun z => ?_)
                  simp only; ring_nf
                have he : stdNormalCDF = fun x => (1 / Real.sqrt (2 * Real.pi)) *
                    ((∫ z in Set.Iic 0, Real.exp (-z ^ 2 / 2)) + ∫ z in (0:ℝ)..x, Real.exp (-z ^ 2 / 2)) := by
                  funext x
                  unfold stdNormalCDF
                  rw [← intervalIntegral.integral_Iic_sub_Iic hI.integrableOn hI.integrableOn]
                  ring
                rw [he]
                exact continuous_const.mul (continuous_const.add
                  (intervalIntegral.continuous_primitive (fun a b => hI.intervalIntegrable) 0))
              have hΦpos : ∀ t, 0 < stdNormalCDF t := by
                intro t
                unfold stdNormalCDF
                have hI : Integrable (fun z : ℝ => Real.exp (-z ^ 2 / 2)) := by
                  have := integrable_exp_neg_mul_sq (b := (1/2 : ℝ)) (by norm_num)
                  refine this.congr (Eventually.of_forall fun z => ?_)
                  simp only; ring_nf
                have : 0 < ∫ z in Set.Iic t, Real.exp (-z ^ 2 / 2) := by
                  rw [integral_pos_iff_support_of_nonneg (fun z => (Real.exp_pos _).le) hI.integrableOn]
                  have hs : Function.support (fun z : ℝ => Real.exp (-z ^ 2 / 2)) = Set.univ :=
                    Set.eq_univ_of_forall fun z => (Real.exp_pos _).ne'
                  rw [hs, Measure.restrict_apply_univ, Real.volume_Iic]
                  simp
                have hpi : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
                positivity
              -- gaussian cdf
              have hGcdf : ∀ (m s w : ℝ), 0 < s →
                  (gaussianReal m (s ^ 2).toNNReal).real (Set.Iic w) = stdNormalCDF ((w - m) / s) := by
                intro m s w hs
                have hmap : gaussianReal m (s ^ 2).toNNReal =
                    (gaussianReal 0 1).map (fun z => s * z + m) := by
                  change _ = Measure.map ((fun x => x + m) ∘ fun x => s * x) _
                  rw [← Measure.map_map (measurable_add_const m) (measurable_const_mul _)]
                  rw [gaussianReal_map_const_mul, gaussianReal_map_add_const]
                  congr 1
                  · simp
                  · ext; simp; positivity
                have hpre : (fun z => s * z + m) ⁻¹' Set.Iic w = Set.Iic ((w - m) / s) := by
                  ext z; simp only [Set.mem_preimage, Set.mem_Iic, le_div_iff₀ hs]; constructor <;> intro h <;> linarith
                rw [hmap, map_measureReal_apply (by fun_prop) measurableSet_Iic, hpre, hΦreal]
              have hp0 : 0 ≤ p := by
                have h := hp 0 le_rfl
                have := hΦpos ((M.θ - p) / M.σ)
                simp only [zero_mul] at h
                by_contra hneg; push Not at hneg
                have : p * stdNormalCDF ((M.θ - p) / M.σ) < 0 := mul_neg_of_neg_of_pos hneg this
                linarith
              have hpost : ∀ x, M.posterior x = gaussianReal (M.postMean x) (sv ^ 2).toNNReal := by
                intro x; rw [Model.posterior, hsq]
              have hrstar_mem : ∀ w v, rstar w v ∈ Set.Icc 0 p := by
                intro w v
                by_cases hv : v ∈ Set.Iic w
                · simp only [hrstar, Set.indicator_of_mem hv]; exact ⟨hp0, le_rfl⟩
                · simp only [hrstar, Set.indicator_of_notMem hv]; exact ⟨le_rfl, hp0⟩
              have hCRstar : ∀ w x, M.condReward (rstar w) x = p * stdNormalCDF ((w - M.postMean x) / sv) := by
                intro w x
                rw [Model.condReward, hpost, integral_indicator_const _ measurableSet_Iic, hGcdf _ _ _ hsvpos,
                  smul_eq_mul, mul_comm]
              have hfeas : ∀ u, FeasibleSC M p (rstar (wu u)) (cu u) := by
                intro u
                refine ⟨⟨measurable_const.indicator measurableSet_Iic, hrstar_mem _⟩, fun v w => ?_, ?_⟩
                · have := (hrstar_mem (wu u) v).2; have := (hrstar_mem (wu u) w).1; linarith
                · rw [hCRstar]
                  have : (wu u - M.postMean (cu u)) / sv = u := by
                    simp only [hwu]; field_simp; ring
                  rw [this]; simp only [hcu]; ring
              have hfeas0 : FeasibleSC M p (fun _ => 0) p := by
                refine ⟨⟨measurable_const, fun _ => ⟨le_rfl, hp0⟩⟩, fun v w => by simp; linarith, ?_⟩
                simp [Model.condReward]
              have hCRb : ∀ r, IsAdmissibleReward p r → ∀ x, 0 ≤ M.condReward r x ∧ M.condReward r x ≤ p := by
                intro r hr x
                refine ⟨integral_nonneg fun v => (hr.2 v).1, ?_⟩
                rw [Model.condReward, hpost]
                calc ∫ v, r v ∂(gaussianReal (M.postMean x) (sv ^ 2).toNNReal) ≤ ∫ _, p ∂(gaussianReal (M.postMean x) (sv ^ 2).toNNReal) := by
                      refine integral_mono_of_nonneg (Eventually.of_forall fun v => (hr.2 v).1)
                        (integrable_const p) (Eventually.of_forall fun v => (hr.2 v).2)
                  _ = p := by simp
              have hcrange : ∀ r c, FeasibleSC M p r c → 0 ≤ c ∧ c ≤ p := by
                rintro r c ⟨hr, -, he⟩
                have := hCRb r hr c
                constructor <;> linarith [this.1, this.2]
              have hprofI : ∀ r c, IsAdmissibleReward p r →
                  Integrable (fun v => (p - r v) * M.salesVolume c v) M.prior := by
                intro r c hr
                unfold Model.prior
                refine Integrable.of_bound ((measurable_const.sub hr.1).mul
                  (hΦcont.measurable.comp ((measurable_id.sub_const c).div_const _))).aestronglyMeasurable p
                  (Eventually.of_forall fun v => ?_)
                have h1 := hr.2 v
                have h2 := hΦ01 ((v - c) / M.σε)
                unfold Model.salesVolume
                rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith [h1.2]) h2.1)]
                calc (p - r v) * stdNormalCDF ((v - c) / M.σε) ≤ p * 1 :=
                      mul_le_mul (by linarith [h1.1]) h2.2 h2.1 hp0
                  _ = p := mul_one p
              have hprofnn : ∀ r c, IsAdmissibleReward p r → 0 ≤ M.expectedProfit p r c := by
                intro r c hr
                refine integral_nonneg fun v => mul_nonneg (by linarith [(hr.2 v).2]) (hΦ01 _).1
              have hcp : ∀ r, FeasibleSC M p r p → M.expectedProfit p r p ≤ P0 := by
                intro r hF
                refine integral_mono (hprofI r p hF.1) (hprofI _ p hfeas0.1) fun v => ?_
                exact mul_le_mul_of_nonneg_right (by linarith [(hF.1.2 v).1]) (hΦ01 _).1
              have hPnn : ∀ u, 0 ≤ P u := fun u => hprofnn _ _ (hfeas u).1
              have hP0nn : 0 ≤ P0 := hprofnn _ _ hfeas0.1
              have hsurj : ∀ c ∈ Set.Ioo 0 p, ∃ u, cu u = c := by
                rintro c ⟨hc1, hc2⟩
                have hpp : 0 < p := hc1.trans hc2
                have ht1 : 0 < 1 - c / p := by rw [sub_pos, div_lt_one hpp]; exact hc2
                have ht2 : 1 - c / p < 1 := by have := div_pos hc1 hpp; linarith
                obtain ⟨a, ha⟩ := (hΦbot.eventually (gt_mem_nhds ht1)).exists
                obtain ⟨b, hb⟩ := (hΦtop.eventually (lt_mem_nhds ht2)).exists
                obtain ⟨u, hu⟩ := intermediate_value_univ a b hΦcont ⟨ha.le, hb.le⟩
                refine ⟨u, ?_⟩
                simp only [hcu, hu]; field_simp; ring
              have hc0 : ∀ r, FeasibleSC M p r 0 → M.expectedProfit p r 0 = 0 := by
                rintro r ⟨hr, -, he⟩
                have hv0 : (sv ^ 2).toNNReal ≠ 0 := by simp; positivity
                have he' : ∫ v, r v ∂(gaussianReal (M.postMean 0) (sv ^ 2).toNNReal) = p := by
                  rw [Model.condReward, hpost] at he; linarith
                have hint : Integrable (fun v => p - r v) (gaussianReal (M.postMean 0) (sv ^ 2).toNNReal) :=
                  Integrable.of_bound (measurable_const.sub hr.1).aestronglyMeasurable p
                    (Eventually.of_forall fun v => by
                      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [(hr.2 v).2])]; linarith [(hr.2 v).1])
                have hrint : Integrable r (gaussianReal (M.postMean 0) (sv ^ 2).toNNReal) :=
                  Integrable.of_bound hr.1.aestronglyMeasurable p
                    (Eventually.of_forall fun v => by
                      rw [Real.norm_eq_abs, abs_of_nonneg (hr.2 v).1]; exact (hr.2 v).2)
                have hz : ∫ v, (p - r v) ∂(gaussianReal (M.postMean 0) (sv ^ 2).toNNReal) = 0 := by
                  rw [integral_sub (integrable_const p) hrint, he']; simp
                have hae := (integral_eq_zero_iff_of_nonneg (fun v => by
                  simp only [Pi.zero_apply]; linarith [(hr.2 v).2]) hint).1 hz
                have hae' : (fun v => p - r v) =ᵐ[volume] 0 := (gaussianReal_absolutelyContinuous' _ hv0).ae_le hae
                have hpri : M.prior ≪ volume := by
                  unfold Model.prior; exact gaussianReal_absolutelyContinuous _ (by simp; positivity)
                unfold Model.expectedProfit
                rw [integral_eq_zero_of_ae]
                filter_upwards [hpri.ae_le hae'] with v hv
                simp only [Pi.zero_apply] at hv ⊢; rw [hv, zero_mul]
              have hRf : Monotone (fun t => stdNormalCDF t * Real.exp (t ^ 2 / 2)) := by
                  clear hc0 hcp hprofI hcrange hCRb hfeas0 hfeas hCRstar hrstar_mem hpost hGcdf hdens hp
                  have hI : Integrable (fun z : ℝ => Real.exp (-z ^ 2 / 2)) := by
                    have := integrable_exp_neg_mul_sq (b := (1/2 : ℝ)) (by norm_num)
                    refine this.congr (Eventually.of_forall fun z => ?_)
                    simp only; ring_nf
                  have hpt : ∀ t y, Set.indicator (Set.Iic t) (fun z : ℝ => Real.exp (-z ^ 2 / 2)) (t - y) *
                      Real.exp (t ^ 2 / 2) = Set.indicator (Set.Ici 0) (fun y => Real.exp (t * y - y ^ 2 / 2)) y := by
                    intro t y
                    by_cases hy : 0 ≤ y
                    · rw [Set.indicator_of_mem (show t - y ∈ Set.Iic t from
                        show t - y ≤ t by linarith only [hy]),
                        Set.indicator_of_mem (show y ∈ Set.Ici 0 from hy), ← Real.exp_add]
                      congr 1; ring
                    · rw [Set.indicator_of_notMem (show t - y ∉ Set.Iic t from
                        fun h => hy (by have : t - y ≤ t := h; linarith only [this])),
                        Set.indicator_of_notMem (show y ∉ Set.Ici 0 from hy), zero_mul]
                  have hrep : ∀ t, stdNormalCDF t * Real.exp (t ^ 2 / 2) = (1 / Real.sqrt (2 * Real.pi)) *
                      ∫ y, Set.indicator (Set.Ici 0) (fun y => Real.exp (t * y - y ^ 2 / 2)) y := by
                    intro t
                    unfold stdNormalCDF
                    rw [mul_assoc, ← integral_indicator measurableSet_Iic, ← integral_mul_const,
                      ← integral_sub_left_eq_self _ volume t]
                    simp only [hpt]
                  have hint : ∀ t, Integrable (fun y => Set.indicator (Set.Ici 0) (fun y => Real.exp (t * y - y ^ 2 / 2)) y) :=
                    fun t => ((hI.indicator (measurableSet_Iic (a := t))).comp_sub_left t |>.mul_const
                      (Real.exp (t ^ 2 / 2))).congr (Eventually.of_forall fun y => hpt t y)
                  intro a b hab
                  simp only
                  rw [hrep, hrep]
                  refine mul_le_mul_of_nonneg_left (integral_mono_of_nonneg (Eventually.of_forall fun y =>
                    Set.indicator_nonneg (fun y _ => (Real.exp_pos _).le) y) (hint b)
                    (Eventually.of_forall fun y => ?_)) (by positivity)
                  by_cases hy : 0 ≤ y
                  · simp only [Set.indicator_of_mem (show y ∈ Set.Ici 0 from hy)]
                    have := mul_le_mul_of_nonneg_right hab hy
                    exact Real.exp_le_exp.2 (by linarith only [this])
                  · simp only [Set.indicator_of_notMem (show y ∉ Set.Ici 0 from hy)]; exact le_rfl

              have hNP : ∀ r c u, FeasibleSC M p r c → cu u = c → M.expectedProfit p r c ≤ P u := by
                clear hΦreal hΦcdf hΦtop hΦbot hΦcont hΦpos hGcdf hc0 hcp hcrange hCRb hfeas0 hsurj hprofnn hPnn hP0nn hCRstar hp hspread
                have hε := hM.σε_pos
                have hθ := hM.σθ_pos
                set Rf : ℝ → ℝ := fun t => stdNormalCDF t * Real.exp (t ^ 2 / 2) with hRfdef
                set K : ℝ → ℝ := fun c => Real.sqrt (2 * Real.pi) * M.σε *
                  gaussianPDFReal M.θ (M.σε ^ 2 + M.σθ ^ 2).toNNReal c with hK
                have hgK : ∀ c v, gaussianPDFReal M.θ (M.σθ ^ 2).toNNReal v * stdNormalCDF ((v - c) / M.σε) =
                    K c * Rf ((v - c) / M.σε) * gaussianPDFReal (M.postMean c) (sv ^ 2).toNNReal v := by
                  intro c v
                  have h1 := hdens M.θ M.σθ M.σε c v hθ hε
                  have hpm : M.σθ ^ 2 / (M.σε ^ 2 + M.σθ ^ 2) * c + (1 - M.σθ ^ 2 / (M.σε ^ 2 + M.σθ ^ 2)) * M.θ
                      = M.postMean c := rfl
                  have hvv : M.σε ^ 2 * M.σθ ^ 2 / (M.σε ^ 2 + M.σθ ^ 2) = sv ^ 2 := hsq
                  rw [hpm, hvv] at h1
                  have hφ : gaussianPDFReal v (M.σε ^ 2).toNNReal c *
                      (Real.sqrt (2 * Real.pi) * M.σε * Real.exp (((v - c) / M.σε) ^ 2 / 2)) = 1 := by
                    rw [gaussianPDFReal_def, Real.coe_toNNReal _ (sq_nonneg _),
                      Real.sqrt_mul (by positivity), Real.sqrt_sq hε.le]
                    have hpi : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
                    have : Real.exp (-(c - v) ^ 2 / (2 * M.σε ^ 2)) * Real.exp (((v - c) / M.σε) ^ 2 / 2) = 1 := by
                      rw [← Real.exp_add, ← Real.exp_zero]; congr 1; field_simp; ring
                    have hne : Real.sqrt (2 * Real.pi) * M.σε ≠ 0 := (mul_pos hpi hε).ne'
                    calc (Real.sqrt (2 * Real.pi) * M.σε)⁻¹ * Real.exp (-(c - v) ^ 2 / (2 * M.σε ^ 2)) *
                          (Real.sqrt (2 * Real.pi) * M.σε * Real.exp (((v - c) / M.σε) ^ 2 / 2))
                        = ((Real.sqrt (2 * Real.pi) * M.σε)⁻¹ * (Real.sqrt (2 * Real.pi) * M.σε)) *
                          (Real.exp (-(c - v) ^ 2 / (2 * M.σε ^ 2)) * Real.exp (((v - c) / M.σε) ^ 2 / 2)) := by ring
                      _ = 1 := by rw [inv_mul_cancel₀ hne, this, one_mul]
                  simp only [hK, hRfdef]
                  calc gaussianPDFReal M.θ (M.σθ ^ 2).toNNReal v * stdNormalCDF ((v - c) / M.σε)
                      = (gaussianPDFReal M.θ (M.σθ ^ 2).toNNReal v * gaussianPDFReal v (M.σε ^ 2).toNNReal c) *
                        (Real.sqrt (2 * Real.pi) * M.σε * Real.exp (((v - c) / M.σε) ^ 2 / 2)) *
                          stdNormalCDF ((v - c) / M.σε) := by rw [mul_assoc _ (gaussianPDFReal _ _ c), hφ, mul_one]
                    _ = _ := by rw [h1]; ring
                intro r c u hF hu
                obtain ⟨hr, -, he⟩ := hF
                set w := wu u with hw
                have hsv0 : (sv ^ 2).toNNReal ≠ 0 := by simp; positivity
                have hθ0 : (M.σθ ^ 2).toNNReal ≠ 0 := by simp; positivity
                -- constraint values
                have hCRr : ∫ v, r v ∂(gaussianReal (M.postMean c) (sv ^ 2).toNNReal) = p - c := by
                  rw [← hpost]; unfold Model.condReward at he; linarith
                have hCRs : ∫ v, rstar w v ∂(gaussianReal (M.postMean c) (sv ^ 2).toNNReal) = p - c := by
                  have := (hfeas u).2.2
                  rw [hu] at this
                  rw [← hpost]; unfold Model.condReward at this; linarith
                have hbd : ∀ v, |r v - rstar w v| ≤ p := by
                  intro v; have h1 := hr.2 v; have h2 := hrstar_mem w v
                  rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
                have hsm : Measurable (rstar w) := by rw [hrstar]; exact measurable_const.indicator measurableSet_Iic
                have hdm : Measurable (fun v => r v - rstar w v) := hr.1.sub hsm
                have hint_h : Integrable (fun v => gaussianPDFReal (M.postMean c) (sv ^ 2).toNNReal v * (r v - rstar w v)) :=
                  (integrable_gaussianPDFReal _ _).mul_bdd hdm.aestronglyMeasurable
                    (Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact hbd v)
                have hzero : ∫ v, gaussianPDFReal (M.postMean c) (sv ^ 2).toNNReal v * (r v - rstar w v) = 0 := by
                  have hir : Integrable r (gaussianReal (M.postMean c) (sv ^ 2).toNNReal) :=
                    Integrable.of_bound hr.1.aestronglyMeasurable p (Eventually.of_forall fun v => by
                      rw [Real.norm_eq_abs, abs_of_nonneg (hr.2 v).1]; exact (hr.2 v).2)
                  have his : Integrable (rstar w) (gaussianReal (M.postMean c) (sv ^ 2).toNNReal) :=
                    Integrable.of_bound hsm.aestronglyMeasurable p (Eventually.of_forall fun v => by
                      rw [Real.norm_eq_abs, abs_of_nonneg (hrstar_mem w v).1]; exact (hrstar_mem w v).2)
                  have := integral_sub hir his
                  rw [hCRr, hCRs, sub_self, integral_gaussianReal_eq_integral_smul hsv0] at this
                  rw [← this]; simp only [smul_eq_mul, Pi.sub_apply]
                have hint_g : Integrable (fun v => gaussianPDFReal M.θ (M.σθ ^ 2).toNNReal v *
                    ((r v - rstar w v) * stdNormalCDF ((v - c) / M.σε))) := by
                  have hm : Measurable (fun v => (r v - rstar w v) * stdNormalCDF ((v - c) / M.σε)) :=
                    hdm.mul (hΦmono.measurable.comp ((measurable_id.sub_const c).div_const _))
                  refine (integrable_gaussianPDFReal M.θ (M.σθ ^ 2).toNNReal).mul_bdd (c := p) hm.aestronglyMeasurable
                    (Eventually.of_forall fun v => ?_)
                  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hΦ01 _).1]
                    calc |r v - rstar w v| * stdNormalCDF ((v - c) / M.σε) ≤ p * 1 :=
                          mul_le_mul (hbd v) (hΦ01 _).2 (hΦ01 _).1 hp0
                      _ = p := mul_one p
                have hkey : 0 ≤ ∫ v, gaussianPDFReal M.θ (M.σθ ^ 2).toNNReal v *
                    ((r v - rstar w v) * stdNormalCDF ((v - c) / M.σε)) := by
                  have hK0 : 0 ≤ K c := by simp only [hK]; exact mul_nonneg (by positivity) (gaussianPDFReal_nonneg _ _ _)
                  calc (0:ℝ) = (K c * Rf ((w - c) / M.σε)) *
                        ∫ v, gaussianPDFReal (M.postMean c) (sv ^ 2).toNNReal v * (r v - rstar w v) := by
                          rw [hzero, mul_zero]
                    _ = ∫ v, (K c * Rf ((w - c) / M.σε)) *
                        (gaussianPDFReal (M.postMean c) (sv ^ 2).toNNReal v * (r v - rstar w v)) :=
                          (integral_const_mul _ _).symm
                    _ ≤ _ := by
                      refine integral_mono (hint_h.const_mul _) hint_g fun v => ?_
                      simp only
                      rw [show gaussianPDFReal M.θ (M.σθ ^ 2).toNNReal v *
                          ((r v - rstar w v) * stdNormalCDF ((v - c) / M.σε)) =
                          (gaussianPDFReal M.θ (M.σθ ^ 2).toNNReal v * stdNormalCDF ((v - c) / M.σε)) *
                          (r v - rstar w v) by ring, hgK]
                      have hh := gaussianPDFReal_nonneg (M.postMean c) (sv ^ 2).toNNReal v
                      have hKh : 0 ≤ K c * gaussianPDFReal (M.postMean c) (sv ^ 2).toNNReal v := mul_nonneg hK0 hh
                      have hdiff : (r v - rstar w v) * (Rf ((v - c) / M.σε) - Rf ((w - c) / M.σε)) ≥ 0 := by
                        by_cases hv : v ≤ w
                        · have h1 : rstar w v = p := Set.indicator_of_mem (show v ∈ Set.Iic w from hv) _
                          have h2 : Rf ((v - c) / M.σε) ≤ Rf ((w - c) / M.σε) :=
                            hRf (div_le_div_of_nonneg_right (by linarith) hε.le)
                          rw [h1]
                          exact mul_nonneg_of_nonpos_of_nonpos (by linarith [(hr.2 v).2]) (by linarith)
                        · push Not at hv
                          have h1 : rstar w v = 0 := Set.indicator_of_notMem (show v ∉ Set.Iic w from not_le.2 hv) _
                          have h2 : Rf ((w - c) / M.σε) ≤ Rf ((v - c) / M.σε) :=
                            hRf (div_le_div_of_nonneg_right (by linarith) hε.le)
                          rw [h1]
                          exact mul_nonneg (by linarith [(hr.2 v).1]) (by linarith)
                      have := mul_nonneg hKh hdiff
                      linarith [this]
                -- conclude
                rw [hP]; simp only; rw [hu]
                have hI1 := hprofI r c hr
                have hI2 := hprofI (rstar w) c ⟨hsm, hrstar_mem w⟩
                have hsub : M.expectedProfit p (rstar w) c - M.expectedProfit p r c =
                    ∫ v, gaussianPDFReal M.θ (M.σθ ^ 2).toNNReal v *
                      ((r v - rstar w v) * stdNormalCDF ((v - c) / M.σε)) := by
                  unfold Model.expectedProfit
                  rw [← integral_sub hI2 hI1]
                  unfold Model.prior
                  rw [integral_gaussianReal_eq_integral_smul hθ0]
                  congr 1; ext v; simp only [smul_eq_mul, Model.salesVolume]; ring
                linarith

              obtain ⟨hPcont, hPtop, hPbot⟩ : Continuous P ∧ Tendsto P atTop (𝓝 0) ∧ Tendsto P atBot (𝓝 P0) := by
                clear hΦreal hΦcdf hΦpos hGcdf hc0 hcp hcrange hCRb hfeas0 hsurj hprofnn hPnn hP0nn hCRstar hp hspread hNP hRf hdens hfeas hprofI hpost
                have hε := hM.σε_pos
                have hθ := hM.σθ_pos
                have hτ0 : 0 ≤ M.tau := by unfold Model.tau; positivity
                have hτ1 : M.tau ≤ 1 := by
                  unfold Model.tau; rw [div_le_one (by positivity)]; linarith only [sq_nonneg M.σε]
                have hcu01 : ∀ u, 0 ≤ cu u ∧ cu u ≤ p := by
                  intro u; rw [hcu]; have := hΦ01 u
                  exact ⟨mul_nonneg hp0 (by linarith only [this.2]), mul_le_of_le_one_right hp0 (by linarith only [this.1])⟩
                have hwu_lo : ∀ u, (1 - M.tau) * M.θ + sv * u ≤ wu u := by
                  intro u; rw [hwu]; simp only [Model.postMean]
                  have := mul_nonneg hτ0 (hcu01 u).1; linarith
                have hwu_hi : ∀ u, wu u ≤ M.tau * p + (1 - M.tau) * M.θ + sv * u := by
                  intro u; rw [hwu]; simp only [Model.postMean]
                  have := mul_le_mul_of_nonneg_left (hcu01 u).2 hτ0; linarith
                have hcucont : Continuous cu := by rw [hcu]; exact continuous_const.mul (continuous_const.sub hΦcont)
                have hwucont : Continuous wu := by
                  rw [hwu]; simp only [Model.postMean]
                  exact ((continuous_const.mul hcucont).add continuous_const).add (continuous_const.mul continuous_id)
                set F : ℝ → ℝ → ℝ := fun u v => (p - rstar (wu u) v) * stdNormalCDF ((v - cu u) / M.σε) with hF
                have hPF : P = fun u => ∫ v, F u v ∂M.prior := by rw [hP]; rfl
                have hFm : ∀ u, AEStronglyMeasurable (F u) M.prior := by
                  intro u
                  have : Measurable (rstar (wu u)) := by rw [hrstar]; exact measurable_const.indicator measurableSet_Iic
                  exact ((measurable_const.sub this).mul
                    (hΦmono.measurable.comp ((measurable_id.sub_const _).div_const _))).aestronglyMeasurable
                have hFb : ∀ u v, ‖F u v‖ ≤ p := by
                  intro u v
                  have h1 := hrstar_mem (wu u) v
                  have h2 := hΦ01 ((v - cu u) / M.σε)
                  simp only [hF]
                  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith [h1.2]) h2.1)]
                  calc (p - rstar (wu u) v) * stdNormalCDF ((v - cu u) / M.σε) ≤ p * 1 :=
                        mul_le_mul (by linarith [h1.1]) h2.2 h2.1 hp0
                    _ = p := mul_one p
                have hpriP : IsProbabilityMeasure M.prior := by unfold Model.prior; infer_instance
                have hbi : Integrable (fun _ : ℝ => p) M.prior := integrable_const p
                have hrs_p : ∀ w v, v ≤ w → rstar w v = p := by
                  intro w v h; exact Set.indicator_of_mem (show v ∈ Set.Iic w from h) _
                have hrs_0 : ∀ w v, w < v → rstar w v = 0 := by
                  intro w v h; exact Set.indicator_of_notMem (show v ∉ Set.Iic w from not_le.2 h) _
                have hΦc : ∀ v, Continuous fun u => stdNormalCDF ((v - cu u) / M.σε) := fun v =>
                  hΦcont.comp ((continuous_const.sub hcucont).div_const _)
                refine ⟨?_, ?_, ?_⟩
                · rw [hPF, continuous_iff_continuousAt]
                  intro u0
                  have hpri : M.prior ≪ volume := by
                    unfold Model.prior; exact gaussianReal_absolutelyContinuous _ (by simp; positivity)
                  have hne : ∀ᵐ v ∂M.prior, v ≠ wu u0 := by
                    have h0 : M.prior {wu u0} = 0 := hpri (Real.volume_singleton)
                    rw [ae_iff]; simpa using h0
                  refine continuousAt_of_dominated (bound := fun _ => p) (Eventually.of_forall hFm)
                    (Eventually.of_forall fun u => Eventually.of_forall (hFb u)) hbi ?_
                  filter_upwards [hne] with v hv
                  refine ContinuousAt.mul ?_ (hΦc v).continuousAt
                  rcases lt_or_gt_of_ne hv with h | h
                  · refine (continuousAt_const (y := p - p)).congr ?_
                    filter_upwards [hwucont.continuousAt.eventually (lt_mem_nhds h)] with u hu
                    rw [hrs_p _ _ hu.le]
                  · refine (continuousAt_const (y := p - 0)).congr ?_
                    filter_upwards [hwucont.continuousAt.eventually (gt_mem_nhds h)] with u hu
                    rw [hrs_0 _ _ hu]
                · rw [hPF]
                  have := tendsto_integral_filter_of_dominated_convergence (μ := M.prior) (l := atTop) (F := F)
                    (f := fun _ => 0) (fun _ => p) (Eventually.of_forall hFm)
                    (Eventually.of_forall fun u => Eventually.of_forall (hFb u)) hbi
                    (Eventually.of_forall fun v => by
                      refine tendsto_const_nhds.congr' ?_
                      filter_upwards [eventually_ge_atTop ((v - (1 - M.tau) * M.θ) / sv)] with u hu
                      have : v ≤ wu u := by
                        have := hwu_lo u
                        rw [div_le_iff₀ hsvpos] at hu; linarith
                      simp only [hF]; rw [hrs_p _ _ this, sub_self, zero_mul])
                  simpa using this
                · rw [hPF, hP0]
                  have hculim : Tendsto cu atBot (𝓝 p) := by
                    rw [hcu]
                    have := (tendsto_const_nhds (x := (1:ℝ))).sub hΦbot
                    simpa using this.const_mul p
                  have := tendsto_integral_filter_of_dominated_convergence (μ := M.prior) (l := atBot) (F := F)
                    (f := fun v => (p - (fun _ => (0:ℝ)) v) * M.salesVolume p v) (fun _ => p) (Eventually.of_forall hFm)
                    (Eventually.of_forall fun u => Eventually.of_forall (hFb u)) hbi
                    (Eventually.of_forall fun v => by
                      have hlim : Tendsto (fun u => (p - 0) * stdNormalCDF ((v - cu u) / M.σε)) atBot
                          (𝓝 ((p - 0) * stdNormalCDF ((v - p) / M.σε))) :=
                        ((hΦcont.tendsto _).comp ((tendsto_const_nhds.sub hculim).div_const _)).const_mul _
                      refine hlim.congr' ?_
                      filter_upwards [eventually_le_atBot ((v - M.tau * p - (1 - M.tau) * M.θ) / sv - 1)] with u hu
                      have : wu u < v := by
                        have := hwu_hi u
                        have h2 : u < (v - M.tau * p - (1 - M.tau) * M.θ) / sv := by linarith
                        rw [lt_div_iff₀ hsvpos] at h2; linarith
                      simp only [hF]; rw [hrs_0 _ _ this])
                  exact this

              -- assembly
              have hbound : ∀ B, P0 ≤ B → (∀ u, P u ≤ B) → ∀ r c, FeasibleSC M p r c →
                  M.expectedProfit p r c ≤ B := by
                intro B hB0 hBu r c hF
                obtain ⟨hc1, hc2⟩ := hcrange r c hF
                rcases hc1.lt_or_eq with hc1 | hc1
                · rcases hc2.lt_or_eq with hc2 | hc2
                  · obtain ⟨u, hu⟩ := hsurj c ⟨hc1, hc2⟩
                    exact (hNP r c u hF hu).trans (hBu u)
                  · subst hc2; exact (hcp r hF).trans hB0
                · subst hc1; rw [hc0 r hF]; exact hP0nn.trans hB0
              by_cases hex : ∃ u0, P0 < P u0
              · obtain ⟨u0, hu0⟩ := hex
                have h1 : ∀ᶠ u in atTop, P u < P u0 := hPtop.eventually (gt_mem_nhds (by linarith [hP0nn]))
                have h2 : ∀ᶠ u in atBot, P u < P u0 := hPbot.eventually (gt_mem_nhds hu0)
                obtain ⟨K1, hK1⟩ := eventually_atTop.1 h1
                obtain ⟨K2, hK2⟩ := eventually_atBot.1 h2
                obtain ⟨us, hus, hmax⟩ := (isCompact_Icc (a := min K2 u0) (b := max K1 u0)).exists_isMaxOn
                  ⟨u0, min_le_right _ _, le_max_right _ _⟩ hPcont.continuousOn
                have hall : ∀ u, P u ≤ P us := by
                  intro u
                  have hu0m : P u0 ≤ P us := hmax ⟨min_le_right _ _, le_max_right _ _⟩
                  by_cases hu1 : K1 ≤ u
                  · exact ((hK1 u hu1).le).trans hu0m
                  by_cases hu2 : u ≤ K2
                  · exact ((hK2 u hu2).le).trans hu0m
                  push Not at hu1 hu2
                  exact hmax ⟨(min_le_left _ _).trans hu2.le, hu1.le.trans (le_max_left _ _)⟩
                exact ⟨_, _, hfeas us, hbound (P us) (hu0.le.trans (hall u0)) hall⟩
              · push Not at hex
                exact ⟨_, _, hfeas0, hbound P0 le_rfl hex⟩
            · rintro r c ⟨hF, hopt⟩
              exact ⟨hSC3 r c hF, fun r' c' h' => hopt r' c' (h3SC r' c' h')⟩
          · intro θ σ p hσ hmp
            set U : ℝ := ∫ x, Set.indicator (Set.Ioi 0) (fun x => min x p) x
              ∂(gaussianReal θ (σ ^ 2).toNNReal) with hU
            have hΦ : ∀ t, 0 < stdNormalCDF t := by
              intro t
              unfold stdNormalCDF
              have hI : Integrable (fun z : ℝ => Real.exp (-z ^ 2 / 2)) := by
                have := integrable_exp_neg_mul_sq (b := (1/2 : ℝ)) (by norm_num)
                refine this.congr (Eventually.of_forall fun z => ?_)
                simp only; ring_nf
              have : 0 < ∫ z in Set.Iic t, Real.exp (-z ^ 2 / 2) := by
                rw [integral_pos_iff_support_of_nonneg (fun z => (Real.exp_pos _).le) hI.integrableOn]
                have hs : Function.support (fun z : ℝ => Real.exp (-z ^ 2 / 2)) = Set.univ :=
                  Set.eq_univ_of_forall fun z => (Real.exp_pos _).ne'
                rw [hs, Measure.restrict_apply_univ, Real.volume_Iic]
                simp
              have hpi : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
              positivity
            have hp : 0 < p := by
              have h := hmp (σ / 2) ⟨by linarith, by linarith⟩ 1 zero_le_one
              by_contra hp; push Not at hp
              have h1 := hΦ (((famModel θ σ (σ / 2)).θ - 1) / (famModel θ σ (σ / 2)).σ)
              have h2 := hΦ (((famModel θ σ (σ / 2)).θ - p) / (famModel θ σ (σ / 2)).σ)
              have h3 := mul_nonpos_of_nonpos_of_nonneg hp h2.le
              linarith only [h, h1, h3]
            have hUpos : 0 < U := by
              set s2 : NNReal := (σ ^ 2).toNNReal with hs2
              have hs2ne : s2 ≠ 0 := by simp [hs2]; positivity
              rw [hU, integral_gaussianReal_eq_integral_smul hs2ne]
              have hmeas : Measurable (fun x : ℝ => Set.indicator (Set.Ioi 0) (fun x => min x p) x) :=
                (measurable_id.min measurable_const).indicator measurableSet_Ioi
              have hbd : ∀ x, ‖Set.indicator (Set.Ioi (0:ℝ)) (fun x => min x p) x‖ ≤ p := by
                intro x
                by_cases hx : x ∈ Set.Ioi (0:ℝ)
                · rw [Set.indicator_of_mem hx, Real.norm_eq_abs, abs_le]
                  have : (0:ℝ) < x := hx
                  constructor <;> [skip; exact min_le_right _ _]
                  have := le_min this.le hp.le; linarith
                · rw [Set.indicator_of_notMem hx]; simp; exact hp.le
              have hint : Integrable (fun x => gaussianPDFReal θ s2 x • Set.indicator (Set.Ioi (0:ℝ)) (fun x => min x p) x) :=
                (integrable_gaussianPDFReal θ s2).mul_bdd hmeas.aestronglyMeasurable (Eventually.of_forall hbd)
              have hnn : ∀ x, 0 ≤ Set.indicator (Set.Ioi (0:ℝ)) (fun x => min x p) x := fun x =>
                Set.indicator_nonneg (fun x hx => le_min (le_of_lt hx) hp.le) x
              rw [integral_pos_iff_support_of_nonneg (fun x => smul_nonneg (gaussianPDFReal_nonneg _ _ _) (hnn x)) hint]
              have hsub : Set.Ioi (0:ℝ) ⊆ Function.support
                  (fun x => gaussianPDFReal θ s2 x • Set.indicator (Set.Ioi (0:ℝ)) (fun x => min x p) x) := by
                intro x hx
                rw [Function.mem_support, Set.indicator_of_mem hx, smul_eq_mul]
                exact (mul_pos (gaussianPDFReal_pos _ _ _ hs2ne) (lt_min hx hp)).ne'
              refine lt_of_lt_of_le ?_ (measure_mono hsub)
              simp
            -- Phi as a gaussian tail
            have hPhi : ∀ v c s : ℝ, 0 < s →
                stdNormalCDF ((v - c) / s) = ∫ x in Set.Ioi c, gaussianPDFReal v (s ^ 2).toNNReal x := by
              intro v c s hs
              have hne : (s ^ 2).toNNReal ≠ 0 := by simp; positivity
              have h1 : ∫ x in Set.Ioi c, gaussianPDFReal v (s ^ 2).toNNReal x =
                  (gaussianReal v (s ^ 2).toNNReal).real (Set.Ioi c) := by
                rw [measureReal_def, gaussianReal_apply_eq_integral _ hne, ENNReal.toReal_ofReal]
                exact setIntegral_nonneg measurableSet_Ioi fun x _ => gaussianPDFReal_nonneg _ _ _
              have hmap : gaussianReal v (s ^ 2).toNNReal =
                  (gaussianReal 0 1).map (fun z => -s * z + v) := by
                change _ = Measure.map ((fun x => x + v) ∘ fun x => -s * x) _
                rw [← Measure.map_map (measurable_add_const v) (measurable_const_mul _)]
                rw [gaussianReal_map_const_mul, gaussianReal_map_add_const]
                congr 1
                · simp
                · ext; simp; positivity
              have hpre : (fun z => -s * z + v) ⁻¹' Set.Ioi c = Set.Iio ((v - c) / s) := by
                ext z; simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_Iio, lt_div_iff₀ hs]; constructor <;> intro h <;> linarith
              rw [h1, hmap, map_measureReal_apply (by fun_prop) measurableSet_Ioi, hpre,
                measureReal_def, gaussianReal_apply_eq_integral _ one_ne_zero, ENNReal.toReal_ofReal
                  (setIntegral_nonneg measurableSet_Iio fun x _ => gaussianPDFReal_nonneg _ _ _),
                ← integral_Iic_eq_integral_Iio]
              unfold stdNormalCDF
              rw [← integral_const_mul]
              refine setIntegral_congr_fun measurableSet_Iic fun z _ => ?_
              simp [gaussianPDFReal_def]
            have hprofit : ∀ (M : Model), M.Valid → ∀ p : ℝ, 0 ≤ p → ∀ r c, Measurable r →
                (∀ v, r v ∈ Set.Icc 0 p) → M.expectedProfit p r c =
                  ∫ x, Set.indicator (Set.Ioi c) (fun x => p - M.condReward r x) x
                    ∂(gaussianReal M.θ (M.σε ^ 2 + M.σθ ^ 2).toNNReal) := by
              intro M hM p hp r c hrm hrb
              have ha := hM.σθ_pos
              have hb := hM.σε_pos
              set a := M.σθ with ha_def
              set b := M.σε with hb_def
              set sa : NNReal := (a ^ 2).toNNReal with hsa
              set sb : NNReal := (b ^ 2).toNNReal with hsb
              set sx : NNReal := (b ^ 2 + a ^ 2).toNNReal with hsx
              set sv : NNReal := (b ^ 2 * a ^ 2 / (b ^ 2 + a ^ 2)).toNNReal with hsv
              have hsa0 : sa ≠ 0 := by simp [hsa]; positivity
              have hsx0 : sx ≠ 0 := by simp [hsx]; positivity
              have hsv0 : sv ≠ 0 := by simp [hsv]; positivity
              have hpost : ∀ x, M.posterior x = gaussianReal
                  (a ^ 2 / (b ^ 2 + a ^ 2) * x + (1 - a ^ 2 / (b ^ 2 + a ^ 2)) * M.θ) sv := by
                intro x; rfl
              have hrn : ∀ v, ‖p - r v‖ ≤ p := fun v => by
                rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hrb v).1, (hrb v).2]
              set G : ℝ × ℝ → ℝ := fun z => gaussianPDFReal M.θ sa z.1 * gaussianPDFReal z.1 sb z.2 * (p - r z.1)
                with hG
              set F : ℝ × ℝ → ℝ := Set.indicator (Prod.snd ⁻¹' Set.Ioi c) G with hF
              have hm1 : Measurable fun z : ℝ × ℝ => gaussianPDFReal M.θ sa z.1 * gaussianPDFReal z.1 sb z.2 := by
                simp only [gaussianPDFReal_def]; fun_prop
              have hGm : Measurable G := hm1.mul (measurable_const.sub (hrm.comp measurable_fst))
              have hH : Integrable (fun z : ℝ × ℝ => gaussianPDFReal M.θ sa z.1 * gaussianPDFReal z.1 sb z.2)
                  (volume.prod volume) := by
                rw [integrable_prod_iff]
                · constructor
                  · exact Eventually.of_forall fun v => by
                      simpa using (integrable_gaussianPDFReal v sb).const_mul (gaussianPDFReal M.θ sa v)
                  · refine (integrable_gaussianPDFReal M.θ sa).congr (Eventually.of_forall fun v => ?_)
                    simp only
                    rw [integral_congr_ae (g := fun x => gaussianPDFReal M.θ sa v * gaussianPDFReal v sb x)
                      (Eventually.of_forall fun x => by
                        simp only [Real.norm_eq_abs]
                        exact abs_of_nonneg (mul_nonneg (gaussianPDFReal_nonneg _ _ _) (gaussianPDFReal_nonneg _ _ _))),
                      integral_const_mul, integral_gaussianPDFReal_eq_one v (by simp [hsb]; positivity), mul_one]
                · exact hm1.aestronglyMeasurable
              have hGi : Integrable G (volume.prod volume) := by
                refine (hH.mul_const p).mono hGm.aestronglyMeasurable (Eventually.of_forall fun z => ?_)
                simp only [hG, norm_mul]
                rw [Real.norm_eq_abs p, abs_of_nonneg hp]
                exact mul_le_mul_of_nonneg_left (hrn _) (by positivity)
              have hFi : Integrable F (volume.prod volume) :=
                hGi.indicator (measurableSet_Ioi.preimage measurable_snd)
              have hCR0 : ∀ x, 0 ≤ M.condReward r x := fun x => integral_nonneg fun v => (hrb v).1
              have hFsl : ∀ v x, F (v, x) = Set.indicator (Set.Ioi c) (fun x => G (v, x)) x := by
                intro v x; simp only [hF, Set.indicator, Set.mem_preimage]
              have hL : M.expectedProfit p r c = ∫ v, ∫ x, F (v, x) := by
                unfold Model.expectedProfit Model.prior Model.salesVolume
                rw [integral_gaussianReal_eq_integral_smul hsa0]
                refine integral_congr_ae (Eventually.of_forall fun v => ?_)
                simp only [hFsl]
                rw [integral_indicator (measurableSet_Ioi : MeasurableSet (Set.Ioi c)), hPhi v c b hb, smul_eq_mul]
                simp only [hG]
                rw [← integral_const_mul, ← integral_const_mul]
                refine setIntegral_congr_fun (measurableSet_Ioi : MeasurableSet (Set.Ioi c)) fun x _ => ?_
                simp only [hsb]; ring
              have hinner : ∀ x, ∫ v, F (v, x) =
                  gaussianPDFReal M.θ sx x * Set.indicator (Set.Ioi c) (fun x => p - M.condReward r x) x := by
                intro x
                by_cases hx : x ∈ Set.Ioi c
                · simp only [hFsl, Set.indicator_of_mem hx, hG]
                  rw [Model.condReward, hpost, integral_gaussianReal_eq_integral_smul hsv0]
                  have hi1 : Integrable (fun v => gaussianPDFReal
                      (a ^ 2 / (b ^ 2 + a ^ 2) * x + (1 - a ^ 2 / (b ^ 2 + a ^ 2)) * M.θ) sv v * r v) :=
                    (integrable_gaussianPDFReal _ sv).mul_bdd hrm.aestronglyMeasurable
                      (Eventually.of_forall fun v => show ‖r v‖ ≤ p by
                        rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hrb v).1, (hrb v).2])
                  simp only [smul_eq_mul]
                  set m := a ^ 2 / (b ^ 2 + a ^ 2) * x + (1 - a ^ 2 / (b ^ 2 + a ^ 2)) * M.θ with hm
                  calc ∫ v, gaussianPDFReal M.θ sa v * gaussianPDFReal v sb x * (p - r v)
                      = ∫ v, (gaussianPDFReal M.θ sx x * gaussianPDFReal m sv v * p -
                          gaussianPDFReal M.θ sx x * (gaussianPDFReal m sv v * r v)) := by
                        refine integral_congr_ae (Eventually.of_forall fun v => ?_)
                        simp only
                        rw [hdens M.θ a b x v ha hb]; ring
                    _ = (∫ v, gaussianPDFReal M.θ sx x * gaussianPDFReal m sv v * p) -
                          ∫ v, gaussianPDFReal M.θ sx x * (gaussianPDFReal m sv v * r v) :=
                        integral_sub (((integrable_gaussianPDFReal m sv).const_mul _).mul_const _) (hi1.const_mul _)
                    _ = _ := by
                        rw [integral_mul_const, integral_const_mul, integral_const_mul,
                          integral_gaussianPDFReal_eq_one _ hsv0]; ring
                · simp only [hFsl, Set.indicator_of_notMem hx, integral_zero, mul_zero]
              have hRi : Integrable (fun x => ∫ v, F (v, x)) := hFi.integral_prod_right
              rw [hL, integral_integral_swap (f := fun v x => F (v, x)) hFi, integral_gaussianReal_eq_integral_smul hsx0]
              refine integral_congr_ae (Eventually.of_forall fun x => ?_)
              simp only [smul_eq_mul]
              exact hinner x
            have hupgen : ∀ (M : Model), M.Valid → ∀ p : ℝ, 0 ≤ p → ∀ r c, Feasible3 M p r c →
                M.expectedProfit p r c ≤ ∫ x, Set.indicator (Set.Ioi 0) (fun x => min x p) x
                  ∂(gaussianReal M.θ (M.σε ^ 2 + M.σθ ^ 2).toNNReal) := by
              intro M hM p hp r c ⟨⟨hrm, hrb⟩, heq1, heq2⟩
              rw [hprofit M hM p hp r c hrm hrb]
              have hCR0 : ∀ x, 0 ≤ M.condReward r x := fun x => integral_nonneg fun v => (hrb v).1
              have hCRp : ∀ x, M.condReward r x ≤ p := fun x => by
                unfold Model.condReward Model.posterior
                calc _ ≤ ∫ v, p ∂(gaussianReal (M.postMean x) M.σv2.toNNReal) :=
                      integral_mono (Integrable.of_bound hrm.aestronglyMeasurable p (ae_of_all _ fun v => by
                        rw [Real.norm_eq_abs, abs_of_nonneg (hrb v).1]; exact (hrb v).2))
                        (integrable_const p) fun v => (hrb v).2
                  _ = p := by simp
              refine integral_mono_of_nonneg (ae_of_all _ fun x => Set.indicator_nonneg
                (fun x _ => by linarith [hCRp x]) x) ?_ (ae_of_all _ fun x => ?_)
              · exact Integrable.of_bound ((measurable_id.min measurable_const).indicator
                  measurableSet_Ioi).aestronglyMeasurable p (ae_of_all _ fun x => by
                  by_cases hx : x ∈ Set.Ioi (0:ℝ)
                  · rw [Set.indicator_of_mem hx, Real.norm_eq_abs, abs_le]
                    have : (0:ℝ) < x := hx
                    exact ⟨by linarith [le_min this.le hp], min_le_right _ _⟩
                  · rw [Set.indicator_of_notMem hx]; simp; exact hp)
              · by_cases hx : x ∈ Set.Ioi c
                · rw [Set.indicator_of_mem hx]
                  have h1 := heq1 x (le_of_lt hx)
                  have h2 := hCR0 x
                  by_cases hx0 : x ∈ Set.Ioi (0:ℝ)
                  · rw [Set.indicator_of_mem hx0]; exact le_min (by linarith) (by linarith)
                  · rw [Set.indicator_of_notMem hx0]; simp only [Set.mem_Ioi, not_lt] at hx0; linarith
                · rw [Set.indicator_of_notMem hx]
                  exact Set.indicator_nonneg (fun x hx => le_min (le_of_lt hx) hp) x
            have hup3 : ∀ s ∈ Set.Ioo 0 σ, ∀ r c, Feasible3 (famModel θ σ s) p r c →
                (famModel θ σ s).expectedProfit p r c ≤ U := by
              intro s hs r c hF
              have hp0 : 0 ≤ p := le_trans (hF.1.2 0).1 (hF.1.2 0).2
              have hV : (famModel θ σ s).Valid :=
                ⟨by show 0 < Real.sqrt (σ ^ 2 - s ^ 2); exact Real.sqrt_pos.2 (sub_pos.2 (pow_lt_pow_left₀ hs.2 hs.1.le two_ne_zero)),
                  by show 0 < s; exact hs.1⟩
              have := hupgen _ hV p hp0 r c hF
              have hsq : (famModel θ σ s).σε ^ 2 + (famModel θ σ s).σθ ^ 2 = σ ^ 2 := by
                show s ^ 2 + Real.sqrt (σ ^ 2 - s ^ 2) ^ 2 = σ ^ 2
                rw [Real.sq_sqrt (sub_pos.2 (pow_lt_pow_left₀ hs.2 hs.1.le two_ne_zero)).le]; ring
              rw [hsq] at this
              exact this
            have hRCgen : ∀ (M : Model), M.Valid → ∀ (p : ℝ) r c, FeasibleRC M p r c → Feasible3 M p r c := by
              clear hdens hPhi hupgen hup3
              have hLip : ∀ (f : ℝ → ℝ) (D : Set ℝ) (K : ℝ), Continuous f → (∀ a b, (D ∩ Set.Icc a b).Finite) →
                  ContDiffOn ℝ 1 f Dᶜ → (∀ v ∉ D, deriv f v ≤ K) → ∀ x y, x ≤ y → f y - f x ≤ K * (y - x) := by
                intro f D K hf hfin hC hd
                suffices H : ∀ n : ℕ, ∀ x y, x ≤ y → (D ∩ Set.Ioo x y).ncard ≤ n → f y - f x ≤ K * (y - x) from
                  fun x y hxy => H _ x y hxy le_rfl
                intro n
                induction n using Nat.strong_induction_on with
                | _ n ih =>
                intro x y hxy hn
                by_cases h : (D ∩ Set.Ioo x y).Nonempty
                · obtain ⟨d, hdD, hd1, hd2⟩ := h
                  have hfinxy : (D ∩ Set.Ioo x y).Finite :=
                    (hfin x y).subset (Set.inter_subset_inter_right _ Set.Ioo_subset_Icc_self)
                  have h1 : (D ∩ Set.Ioo x d).ncard < (D ∩ Set.Ioo x y).ncard := by
                    apply Set.ncard_lt_ncard _ hfinxy
                    refine ⟨Set.inter_subset_inter_right _ (Set.Ioo_subset_Ioo_right hd2.le), fun hsub => ?_⟩
                    have := (hsub ⟨hdD, hd1, hd2⟩).2.2
                    exact lt_irrefl _ this
                  have h2 : (D ∩ Set.Ioo d y).ncard < (D ∩ Set.Ioo x y).ncard := by
                    apply Set.ncard_lt_ncard _ hfinxy
                    refine ⟨Set.inter_subset_inter_right _ (Set.Ioo_subset_Ioo_left hd1.le), fun hsub => ?_⟩
                    have := (hsub ⟨hdD, hd1, hd2⟩).2.1
                    exact lt_irrefl _ this
                  have e1 := ih _ (lt_of_lt_of_le h1 hn) x d hd1.le le_rfl
                  have e2 := ih _ (lt_of_lt_of_le h2 hn) d y hd2.le le_rfl
                  linarith
                · have hsub : Set.Ioo x y ⊆ Dᶜ := fun z hz hzD => h ⟨z, hzD, hz⟩
                  refine Convex.image_sub_le_mul_sub_of_deriv_le (convex_Icc x y) hf.continuousOn ?_ ?_ x
                    ⟨le_rfl, hxy⟩ y ⟨hxy, le_rfl⟩ hxy
                  · rw [interior_Icc]; exact (hC.differentiableOn one_ne_zero).mono hsub
                  · intro z hz; rw [interior_Icc] at hz; exact hd z (hsub hz)
              intro M hM p r c hF
              obtain ⟨hbd, ⟨D, ⟨hcont, hfin, hC, -⟩, hder⟩, heq⟩ := hF
              have hε := hM.σε_pos
              have hθ := hM.σθ_pos
              have hτ : 0 < M.tau := by unfold Model.tau; positivity
              have hlow : ∀ x y, x ≤ y → -(1 / M.tau) * (y - x) ≤ r y - r x := by
                intro x y hxy
                have := hLip (fun v => -r v) D (1 / M.tau) hcont.neg hfin hC.neg (fun v hv => by
                  have hdn : deriv (fun v => -r v) v = -deriv r v := by
                    exact deriv.neg
                  rw [hdn]; have := hder v hv; rw [abs_le] at this; linarith) x y hxy
                linarith
              have hmono : Monotone (fun x => x - p + M.condReward r x) := by
                intro x y hxy
                simp only
                set s2 : NNReal := M.σv2.toNNReal with hs2
                have hv2pos : 0 < M.σv2 := by unfold Model.σv2; positivity
                have hs2ne : s2 ≠ 0 := by simp [hs2, hv2pos]
                set a := M.postMean x with ha
                set b := M.postMean y with hb
                have hab : b - a = M.tau * (y - x) := by simp only [a, b, Model.postMean]; ring
                have hrb : ∀ v, ‖r v‖ ≤ p := fun v => by
                  rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hbd v).1, (hbd v).2]
                have hmeas : Measurable r := hcont.measurable
                have hint : ∀ μ, Integrable (fun w => gaussianPDFReal μ s2 w * r w) := fun μ =>
                  (integrable_gaussianPDFReal μ s2).mul_bdd hmeas.aestronglyMeasurable
                    (Eventually.of_forall hrb)
                have hCR : ∀ μ, ∫ v, r v ∂(gaussianReal μ s2) = ∫ w, gaussianPDFReal μ s2 w * r w := fun μ => by
                  rw [integral_gaussianReal_eq_integral_smul hs2ne]; simp [smul_eq_mul]
                have hshift : ∫ w, gaussianPDFReal b s2 w * r w = ∫ w, gaussianPDFReal a s2 w * r (w + (b - a)) := by
                  rw [← integral_add_right_eq_self (fun w => gaussianPDFReal b s2 w * r w) (b - a)]
                  congr 1; ext w
                  simp only [gaussianPDFReal_def]; ring_nf
                have hint2 : Integrable (fun w => gaussianPDFReal a s2 w * r (w + (b - a))) :=
                  (integrable_gaussianPDFReal a s2).mul_bdd (hmeas.comp (measurable_add_const _)).aestronglyMeasurable
                    (Eventually.of_forall fun w => hrb _)
                have hdiff : M.condReward r y - M.condReward r x =
                    ∫ w, gaussianPDFReal a s2 w * (r (w + (b - a)) - r w) := by
                  unfold Model.condReward Model.posterior
                  rw [hCR, hCR, hshift, ← integral_sub hint2 (hint _)]
                  congr 1; ext w; ring
                have hge : ∫ w, gaussianPDFReal a s2 w * (-(1 / M.tau) * (b - a)) ≤
                    ∫ w, gaussianPDFReal a s2 w * (r (w + (b - a)) - r w) := by
                  refine integral_mono ((integrable_gaussianPDFReal a s2).mul_const _) (hint2.sub (hint a) |>.congr
                    (Eventually.of_forall fun w => by simp only [Pi.sub_apply]; ring)) fun w => ?_
                  exact mul_le_mul_of_nonneg_left (by
                    have := hlow w (w + (b - a)) (by have := mul_nonneg hτ.le (sub_nonneg.2 hxy); linarith only [this, hab]); simpa using this)
                    (gaussianPDFReal_nonneg a s2 w)
                rw [integral_mul_const, integral_gaussianPDFReal_eq_one a hs2ne] at hge
                have : -(1 / M.tau) * (b - a) = -(y - x) := by rw [hab]; field_simp
                linarith
              refine ⟨⟨hcont.measurable, hbd⟩, fun x hx => ?_, fun x hx => ?_⟩
              · have := hmono hx; simp only at this; linarith
              · have := hmono hx; simp only at this; linarith
            have hRC3 : ∀ s ∈ Set.Ioo 0 σ, ∀ r c, FeasibleRC (famModel θ σ s) p r c →
                Feasible3 (famModel θ σ s) p r c := by
              intro s hs
              exact hRCgen _ ⟨by show 0 < Real.sqrt (σ ^ 2 - s ^ 2); exact Real.sqrt_pos.2 (sub_pos.2 (pow_lt_pow_left₀ hs.2 hs.1.le two_ne_zero)),
                by show 0 < s; exact hs.1⟩ p
            have hlowgen : ∀ (M : Model), M.Valid → ∀ (p : ℝ), 0 < p →
                (∀ r c, Measurable r → (∀ v, r v ∈ Set.Icc 0 p) → M.expectedProfit p r c =
                  ∫ x, Set.indicator (Set.Ioi c) (fun x => p - M.condReward r x) x
                    ∂(gaussianReal M.θ (M.σε ^ 2 + M.σθ ^ 2).toNNReal)) →
                ∃ r c, FeasibleRC M p r c ∧
                  (∫ x, Set.indicator (Set.Ioi 0) (fun x => min x p) x
                    ∂(gaussianReal M.θ (M.σε ^ 2 + M.σθ ^ 2).toNNReal)) - 2 * Real.sqrt M.σv2 / M.tau
                    ≤ M.expectedProfit p r c := by
              clear hdens hPhi hupgen hup3 hRCgen hRC3 hUpos hU hmp hΦ
              intro M hM p hp hprofit
              have hε := hM.σε_pos
              have hθ := hM.σθ_pos
              have hτ : 0 < M.tau := by unfold Model.tau; positivity
              have hv2 : 0 < M.σv2 := by unfold Model.σv2; positivity
              set τ := M.tau with hτdef
              set sv := Real.sqrt M.σv2 with hsvdef
              have hsv : 0 < sv := Real.sqrt_pos.2 hv2
              have hsv2 : ((M.σv2.toNNReal : NNReal) : ℝ) = sv ^ 2 := by
                rw [Real.coe_toNNReal _ hv2.le, hsvdef, Real.sq_sqrt hv2.le]
              have hG : ∀ μ : ℝ, Integrable (fun x => |x - μ|) (gaussianReal μ M.σv2.toNNReal) ∧
                  ∫ x, |x - μ| ∂(gaussianReal μ M.σv2.toNNReal) ≤ sv := by
                intro μ
                clear hprofit
                generalize M.σv2.toNNReal = v at hsv2 ⊢
                have hv := hsv2
                have hL2 : MemLp id 2 (gaussianReal μ v) := memLp_id_gaussianReal 2
                have hI1 : Integrable (fun x : ℝ => x) (gaussianReal μ v) := (memLp_id_gaussianReal 1).integrable le_rfl
                have hIsq : Integrable (fun x => (x - μ) ^ 2) (gaussianReal μ v) := by
                  have := (hL2.sub (memLp_const μ)).integrable_sq
                  simpa using this
                have hIabs : Integrable (fun x => |x - μ|) (gaussianReal μ v) := (hI1.sub (integrable_const μ)).abs
                refine ⟨hIabs, ?_⟩
                have hvar : ∫ x, (x - μ) ^ 2 ∂(gaussianReal μ v) = sv ^ 2 := by
                  have := variance_id_gaussianReal (μ := μ) (v := v)
                  rw [variance_eq_integral measurable_id.aemeasurable] at this
                  simp only [id, integral_id_gaussianReal] at this
                  rw [this, hv]
                have hpt : ∀ x, |x - μ| ≤ ((x - μ) ^ 2 / sv + sv) / 2 := by
                  intro x
                  have h1 : (|x - μ| - sv) ^ 2 ≥ 0 := sq_nonneg _
                  have h2 : |x - μ| ^ 2 = (x - μ) ^ 2 := sq_abs _
                  rw [le_div_iff₀ two_pos, div_add' _ _ _ hsv.ne', le_div_iff₀ hsv]
                  have h3 : (|x - μ| - sv) ^ 2 = |x - μ| ^ 2 - 2 * sv * |x - μ| + sv ^ 2 := by ring
                  have h4 : |x - μ| * 2 * sv = 2 * sv * |x - μ| := by ring
                  have h5 : (x - μ) ^ 2 + sv * sv = (x - μ) ^ 2 + sv ^ 2 := by ring
                  linarith only [h1, h2, h3, h4, h5]
                calc ∫ x, |x - μ| ∂(gaussianReal μ v) ≤ ∫ x, ((x - μ) ^ 2 / sv + sv) / 2 ∂(gaussianReal μ v) :=
                      integral_mono hIabs (((hIsq.div_const sv).add (integrable_const sv)).div_const 2) hpt
                  _ = sv := by
                      rw [integral_div, integral_add (hIsq.div_const sv) (integrable_const sv), integral_div, hvar,
                        integral_const]
                      simp
                      field_simp
                      ring
              set vL := (1 - τ) * M.θ + sv with hvL
              have hrate : ∃ D : Set ℝ, IsPiecewiseC1 (fun v => p - min (max (v - vL) 0) (τ * p) / τ) D ∧
                  ∀ v ∉ D, |deriv (fun v => p - min (max (v - vL) 0) (τ * p) / τ) v| ≤ 1 / τ := by
                clear_value vL τ sv
                clear hG hprofit hsv2
                set r : ℝ → ℝ := fun v => p - min (max (v - vL) 0) (τ * p) / τ with hr
                set vH := vL + τ * p with hvH
                have hτp : 0 < τ * p := mul_pos hτ hp
                have hLH : vL < vH := by rw [hvH]; linarith
                have hA : ∀ y, y < vL → r =ᶠ[𝓝 y] fun _ => p := fun y hy =>
                  Filter.eventuallyEq_of_mem (Iio_mem_nhds hy) fun v (hv : v < vL) => by
                    simp only [hr]
                    rw [max_eq_right (by linarith), min_eq_left hτp.le, zero_div, sub_zero]
                have hB : ∀ y, vL < y → y < vH → r =ᶠ[𝓝 y] fun v => p - (v - vL) / τ := fun y h1 h2 =>
                  Filter.eventuallyEq_of_mem (Ioo_mem_nhds h1 h2) fun v (hv : v ∈ Set.Ioo vL vH) => by
                    simp only [hr]
                    rw [max_eq_left (by linarith [hv.1]), min_eq_left (by linarith [hv.2])]
                have hC : ∀ y, vH < y → r =ᶠ[𝓝 y] fun _ => 0 := fun y hy =>
                  Filter.eventuallyEq_of_mem (Ioi_mem_nhds hy) fun v (hv : vH < v) => by
                    simp only [hr]
                    rw [max_eq_left (by linarith), min_eq_right (by linarith), mul_div_cancel_left₀ _ hτ.ne', sub_self]
                have hBd : ∀ y, HasDerivAt (fun v => p - (v - vL) / τ) (-(1 / τ)) y := fun y => by
                  have := (((hasDerivAt_id y).sub_const vL).div_const τ).const_sub p
                  simpa using this
                have hBc : ContDiff ℝ 1 (fun v : ℝ => p - (v - vL) / τ) := by fun_prop
                have hd : ∀ y, (y < vL → deriv r y = 0) ∧ (vL < y → y < vH → deriv r y = -(1 / τ)) ∧
                    (vH < y → deriv r y = 0) := fun y =>
                  ⟨fun h => by rw [(hA y h).deriv_eq, deriv_const],
                   fun h1 h2 => by rw [(hB y h1 h2).deriv_eq, (hBd y).deriv],
                   fun h => by rw [(hC y h).deriv_eq, deriv_const]⟩
                refine ⟨{vL, vH}, ⟨?_, fun a b => ((Set.toFinite {vL, vH}).subset Set.inter_subset_left), ?_, ?_⟩, ?_⟩
                · simp only [hr]; fun_prop
                · intro y hy
                  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hy
                  rcases lt_or_gt_of_ne hy.1 with h | h
                  · exact (contDiffAt_const.congr_of_eventuallyEq (hA y h)).contDiffWithinAt
                  · rcases lt_or_gt_of_ne hy.2 with h' | h'
                    · exact (hBc.contDiffAt.congr_of_eventuallyEq (hB y h h')).contDiffWithinAt
                    · exact (contDiffAt_const.congr_of_eventuallyEq (hC y h')).contDiffWithinAt
                · intro v hv
                  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
                  rcases hv with rfl | rfl
                  · refine ⟨0, -(1 / τ), ?_, ?_⟩
                    · exact tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun y (hy : y < v) => ((hd y).1 hy).symm)
                    · exact tendsto_const_nhds.congr' (Filter.eventually_of_mem (Ioo_mem_nhdsGT hLH)
                        fun y hy => ((hd y).2.1 hy.1 hy.2).symm)
                  · refine ⟨-(1 / τ), 0, ?_, ?_⟩
                    · exact tendsto_const_nhds.congr' (Filter.eventually_of_mem (Ioo_mem_nhdsLT hLH)
                        fun y hy => ((hd y).2.1 hy.1 hy.2).symm)
                    · exact tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun y (hy : vH < y) => ((hd y).2.2 hy).symm)
                · intro y hy
                  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hy
                  have h0 : (0:ℝ) ≤ 1 / τ := by positivity
                  rcases lt_or_gt_of_ne hy.1 with h | h
                  · rw [(hd y).1 h, abs_zero]; exact h0
                  · rcases lt_or_gt_of_ne hy.2 with h' | h'
                    · rw [(hd y).2.1 h h', abs_neg, abs_of_nonneg h0]
                    · rw [(hd y).2.2 h', abs_zero]; exact h0
              set r : ℝ → ℝ := fun v => p - min (max (v - vL) 0) (τ * p) / τ with hr
              have hrc : Continuous r := by simp only [hr]; fun_prop
              have hrb : ∀ v, r v ∈ Set.Icc 0 p := by
                intro v
                have h1 : 0 ≤ min (max (v - vL) 0) (τ * p) := le_min (le_max_right _ _) (by positivity)
                have h2 : min (max (v - vL) 0) (τ * p) ≤ τ * p := min_le_right _ _
                have h3 : min (max (v - vL) 0) (τ * p) / τ ≤ p := by rw [div_le_iff₀ hτ]; linarith
                have h4 : 0 ≤ min (max (v - vL) 0) (τ * p) / τ := div_nonneg h1 hτ.le
                exact ⟨by simp only [hr]; linarith, by simp only [hr]; linarith⟩
              have hrI : ∀ μ, Integrable r (gaussianReal μ M.σv2.toNNReal) := fun μ =>
                Integrable.of_bound hrc.aestronglyMeasurable p (ae_of_all _ fun v => by
                  rw [Real.norm_eq_abs, abs_of_nonneg (hrb v).1]; exact (hrb v).2)
              have hpost : ∀ x, M.condReward r x = ∫ v, r v ∂(gaussianReal (τ * x + (1 - τ) * M.θ) M.σv2.toNNReal) :=
                fun x => rfl
              have hCR01 : ∀ x, 0 ≤ M.condReward r x ∧ M.condReward r x ≤ p := by
                intro x
                rw [hpost]
                refine ⟨integral_nonneg fun v => (hrb v).1, ?_⟩
                calc _ ≤ ∫ v, p ∂(gaussianReal (τ * x + (1 - τ) * M.θ) M.σv2.toNNReal) :=
                      integral_mono (hrI _) (integrable_const p) fun v => (hrb v).2
                  _ = p := by simp
              have hlo : ∀ x, p - (sv + |τ * x - sv|) / τ ≤ M.condReward r x := by
                intro x
                rw [hpost]
                set μ := τ * x + (1 - τ) * M.θ with hμ
                have hpt : ∀ v, p - (|v - μ| + |τ * x - sv|) / τ ≤ r v := by
                  intro v
                  have hm : μ - vL = τ * x - sv := by rw [hμ, hvL]; ring
                  have h1 : min (max (v - vL) 0) (τ * p) ≤ |v - μ| + |τ * x - sv| := by
                    refine le_trans (min_le_left _ _) (max_le ?_ (by positivity))
                    have := abs_add_le (v - μ) (μ - vL)
                    rw [hm] at this
                    have := le_abs_self (v - μ + (τ * x - sv))
                    linarith
                  simp only [hr]
                  have := div_le_div_of_nonneg_right h1 hτ.le
                  linarith
                have hI : Integrable (fun v => (|v - μ| + |τ * x - sv|) / τ) (gaussianReal μ M.σv2.toNNReal) :=
                  ((hG μ).1.add (integrable_const |τ * x - sv|)).div_const τ
                calc p - (sv + |τ * x - sv|) / τ ≤ p - ((∫ v, |v - μ| ∂(gaussianReal μ M.σv2.toNNReal)) + |τ * x - sv|) / τ := by
                      have h3 : ((∫ v, |v - μ| ∂(gaussianReal μ M.σv2.toNNReal)) + |τ * x - sv|) / τ ≤
                          (sv + |τ * x - sv|) / τ := div_le_div_of_nonneg_right (by linarith [(hG μ).2]) hτ.le
                      linarith
                  _ = ∫ v, (p - (|v - μ| + |τ * x - sv|) / τ) ∂(gaussianReal μ M.σv2.toNNReal) := by
                      rw [integral_sub (integrable_const p) hI, integral_div, integral_add (hG μ).1 (integrable_const _)]
                      simp
                  _ ≤ _ := integral_mono ((integrable_const p).sub hI) (hrI μ) hpt
              have hhi : ∀ x, min x p - 2 * sv / τ ≤ p - M.condReward r x := by
                intro x
                rw [hpost]
                set μ := τ * x + (1 - τ) * M.θ with hμ
                have hpt : ∀ v, (min (τ * x - sv) (τ * p) - |v - μ|) / τ ≤ p - r v := by
                  intro v
                  have hm : μ - vL = τ * x - sv := by rw [hμ, hvL]; ring
                  have h1 : min (τ * x - sv) (τ * p) - |v - μ| ≤ min (max (v - vL) 0) (τ * p) := by
                    have := neg_abs_le (v - μ)
                    rcases le_total (τ * x - sv) (τ * p) with h | h
                    · rw [min_eq_left h]
                      refine le_min ?_ (by linarith [abs_nonneg (v - μ)])
                      refine le_trans ?_ (le_max_left _ _)
                      linarith
                    · rw [min_eq_right h]
                      refine le_min (le_trans (by linarith [abs_nonneg (v - μ)]) (le_max_left _ _)) (by linarith [abs_nonneg (v - μ)])
                  simp only [hr]
                  have := div_le_div_of_nonneg_right h1 hτ.le
                  linarith
                have hI : Integrable (fun v => (min (τ * x - sv) (τ * p) - |v - μ|) / τ) (gaussianReal μ M.σv2.toNNReal) :=
                  ((integrable_const (min (τ * x - sv) (τ * p))).sub (hG μ).1).div_const τ
                have hkey : min x p - 2 * sv / τ ≤ (min (τ * x - sv) (τ * p) - sv) / τ := by
                  rw [le_div_iff₀ hτ]
                  have e1 : (min x p - 2 * sv / τ) * τ = min x p * τ - 2 * sv := by
                    rw [sub_mul, div_mul_cancel₀ _ hτ.ne']
                  rw [e1]
                  have h1 := mul_le_mul_of_nonneg_right (min_le_left x p) hτ.le
                  have h2 := mul_le_mul_of_nonneg_right (min_le_right x p) hτ.le
                  have h3 := le_min (show min x p * τ - sv ≤ τ * x - sv by linarith only [h1])
                    (show min x p * τ - sv ≤ τ * p by linarith only [h2, hsv])
                  linarith only [h3]
                calc min x p - 2 * sv / τ ≤ (min (τ * x - sv) (τ * p) - sv) / τ := hkey
                  _ ≤ (min (τ * x - sv) (τ * p) - ∫ v, |v - μ| ∂(gaussianReal μ M.σv2.toNNReal)) / τ :=
                      div_le_div_of_nonneg_right (by linarith [(hG μ).2]) hτ.le
                  _ = ∫ v, (min (τ * x - sv) (τ * p) - |v - μ|) / τ ∂(gaussianReal μ M.σv2.toNNReal) := by
                      rw [integral_div, integral_sub (integrable_const _) (hG μ).1]
                      simp
                  _ ≤ ∫ v, (p - r v) ∂(gaussianReal μ M.σv2.toNNReal) :=
                      integral_mono hI ((integrable_const p).sub (hrI μ)) hpt
                  _ = _ := by rw [integral_sub (integrable_const p) (hrI μ)]; simp
              have hCRc : Continuous fun x => M.condReward r x := by
                have hmap : ∀ x, gaussianReal (τ * x + (1 - τ) * M.θ) M.σv2.toNNReal =
                    (gaussianReal 0 M.σv2.toNNReal).map (· + (τ * x + (1 - τ) * M.θ)) := fun x => by
                  rw [gaussianReal_map_add_const, zero_add]
                have : (fun x => M.condReward r x) = fun x => ∫ w, r (w + (τ * x + (1 - τ) * M.θ)) ∂(gaussianReal 0 M.σv2.toNNReal) := by
                  funext x
                  rw [hpost, hmap, integral_map (measurable_add_const _).aemeasurable hrc.aestronglyMeasurable]
                rw [this]
                refine continuous_of_dominated (bound := fun _ => p) (fun x => (hrc.comp (continuous_add_const _)).aestronglyMeasurable)
                  (fun x => ae_of_all _ fun w => ?_) (integrable_const p) (ae_of_all _ fun w => by fun_prop)
                rw [Real.norm_eq_abs, abs_of_nonneg (hrb _).1]; exact (hrb _).2
              set cb := 2 * sv / τ with hcb
              have hcb0 : 0 ≤ cb := by positivity
              have hF0 : 0 + M.condReward r 0 - p ≤ 0 := by linarith [(hCR01 0).2]
              have hFc : 0 ≤ cb + M.condReward r cb - p := by
                have := hlo cb
                have e : τ * cb - sv = sv := by rw [hcb]; field_simp; ring
                rw [e, abs_of_pos hsv] at this
                have e2 : (sv + sv) / τ = cb := by rw [hcb]; ring
                linarith
              obtain ⟨c, ⟨hc0, hc1⟩, hFc0⟩ := intermediate_value_Icc hcb0
                ((continuous_id.add hCRc).sub continuous_const).continuousOn ⟨hF0, hFc⟩
              have hFc1 : c + M.condReward r c - p = 0 := hFc0
              refine ⟨r, c, ⟨hrb, hrate, by linarith⟩, ?_⟩
              rw [hprofit r c hrc.measurable hrb]
              set N := gaussianReal M.θ (M.σε ^ 2 + M.σθ ^ 2).toNNReal
              have hUi : Integrable (Set.indicator (Set.Ioi 0) (fun x => min x p)) N :=
                Integrable.of_bound ((measurable_id.min measurable_const).indicator measurableSet_Ioi).aestronglyMeasurable p
                  (ae_of_all _ fun x => by
                    by_cases hx : x ∈ Set.Ioi (0:ℝ)
                    · rw [Set.indicator_of_mem hx, Real.norm_eq_abs, abs_le]
                      have : (0:ℝ) < x := hx
                      exact ⟨by linarith [le_min this.le hp.le], min_le_right _ _⟩
                    · rw [Set.indicator_of_notMem hx]; simp; exact hp.le)
              have hLi : Integrable (Set.indicator (Set.Ioi c) (fun x => p - M.condReward r x)) N :=
                Integrable.of_bound ((measurable_const.sub hCRc.measurable).indicator measurableSet_Ioi).aestronglyMeasurable p
                  (ae_of_all _ fun x => by
                    by_cases hx : x ∈ Set.Ioi c
                    · rw [Set.indicator_of_mem hx, Real.norm_eq_abs, abs_le]
                      exact ⟨by linarith [(hCR01 x).2, (hCR01 x).1], by linarith [(hCR01 x).1]⟩
                    · rw [Set.indicator_of_notMem hx]; simp; exact hp.le)
              calc (∫ x, Set.indicator (Set.Ioi 0) (fun x => min x p) x ∂N) - cb
                  = ∫ x, (Set.indicator (Set.Ioi 0) (fun x => min x p) x - cb) ∂N := by
                    rw [integral_sub hUi (integrable_const cb)]; simp
                _ ≤ _ := by
                  refine integral_mono (hUi.sub (integrable_const cb)) hLi fun x => ?_
                  by_cases hx : x ∈ Set.Ioi c
                  · have hx0 : x ∈ Set.Ioi (0:ℝ) := lt_of_le_of_lt hc0 hx
                    simp only [Set.indicator_of_mem hx, Set.indicator_of_mem hx0]
                    exact hhi x
                  · simp only [Set.indicator_of_notMem hx]
                    by_cases hx0 : x ∈ Set.Ioi (0:ℝ)
                    · simp only [Set.indicator_of_mem hx0]
                      have : x ≤ c := not_lt.1 hx
                      linarith [min_le_left x p]
                    · simp only [Set.indicator_of_notMem hx0]; linarith
            have hlow : ∀ ε > 0, ∀ᶠ s in 𝓝[>] (0:ℝ), ∃ r c, FeasibleRC (famModel θ σ s) p r c ∧
                U - ε < (famModel θ σ s).expectedProfit p r c := by
              intro ε hε
              filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < min (σ / 2) (ε / 3) from lt_min (by linarith) (by linarith))]
                with s hs
              have hs0 : 0 < s := hs.1
              have hs1 : s < σ / 2 := lt_of_lt_of_le hs.2 (min_le_left _ _)
              have hs2 : s < ε / 3 := lt_of_lt_of_le hs.2 (min_le_right _ _)
              clear hdens hPhi hupgen hup3 hRCgen hRC3 hUpos hΦ hmp
              obtain ⟨M, hMdef⟩ : ∃ M, M = famModel θ σ s := ⟨_, rfl⟩
              rw [← hMdef]
              have hMε : M.σε = s := by rw [hMdef]; rfl
              have hMθ : M.σθ = Real.sqrt (σ ^ 2 - s ^ 2) := by rw [hMdef]; rfl
              have hMθ' : M.θ = θ := by rw [hMdef]; rfl
              clear hMdef
              have hss : s * s < σ / 2 * (σ / 2) := mul_self_lt_mul_self hs0.le hs1
              have hd : 0 < σ ^ 2 - s ^ 2 := by linarith only [hss, sq_nonneg σ, hs0, hs1]
              have hV : M.Valid := ⟨by rw [hMθ]; exact Real.sqrt_pos.2 hd, by rw [hMε]; exact hs0⟩
              obtain ⟨r, c, hF, hb⟩ := hlowgen M hV p hp (hprofit M hV p hp.le)
              have hθsq : M.σθ ^ 2 = σ ^ 2 - s ^ 2 := by rw [hMθ]; exact Real.sq_sqrt hd.le
              have hsq : M.σε ^ 2 + M.σθ ^ 2 = σ ^ 2 := by rw [hθsq, hMε]; ring
              have hσ2 : 0 < σ ^ 2 := pow_pos hσ 2
              have htau : M.tau = (σ ^ 2 - s ^ 2) / σ ^ 2 := by unfold Model.tau; rw [hsq, hθsq]
              have hv2 : M.σv2 = s ^ 2 * ((σ ^ 2 - s ^ 2) / σ ^ 2) := by
                unfold Model.σv2; rw [hsq, hθsq, hMε]; ring
              have hτ1 : (σ ^ 2 - s ^ 2) / σ ^ 2 ≤ 1 := by
                rw [div_le_one hσ2]; linarith only [mul_self_nonneg s]
              have hτ34 : 3 / 4 ≤ M.tau := by rw [htau, le_div_iff₀ hσ2]; linarith only [hss, hs0]
              have hsv : Real.sqrt M.σv2 ≤ s :=
                (Real.sqrt_le_sqrt (by rw [hv2]; exact mul_le_of_le_one_right (sq_nonneg s) hτ1)).trans_eq
                  (Real.sqrt_sq hs0.le)
              have herr : 2 * Real.sqrt M.σv2 / M.tau < ε := by
                rw [div_lt_iff₀ (by linarith only [hτ34])]
                linarith only [hsv, hτ34, hs2, hε, mul_le_mul_of_nonneg_left hτ34 hε.le]
              rw [hsq, hMθ'] at hb
              exact ⟨r, c, hF, by linarith only [hb, herr]⟩
            have hIoo : ∀ᶠ s in 𝓝[>] (0:ℝ), s ∈ Set.Ioo 0 σ := Ioo_mem_nhdsGT hσ
            have hRC : Tendsto (fun s => optValueRC (famModel θ σ s) p) (𝓝[>] 0) (𝓝 U) := by
              rw [tendsto_order]; constructor
              · intro a ha
                filter_upwards [hlow (U - a) (by linarith only [ha]), hIoo] with s ⟨r, c, hF, hπ⟩ hs
                refine lt_of_lt_of_le (by linarith only [hπ]) (le_csSup ⟨U, ?_⟩ ⟨r, c, hF, rfl⟩)
                rintro _ ⟨r', c', hF', rfl⟩; exact hup3 s hs r' c' (hRC3 s hs r' c' hF')
              · intro a ha
                filter_upwards [hlow 1 one_pos, hIoo] with s ⟨r, c, hF, hπ⟩ hs
                refine lt_of_le_of_lt (csSup_le ⟨_, r, c, hF, rfl⟩ ?_) ha
                rintro _ ⟨r', c', hF', rfl⟩; exact hup3 s hs r' c' (hRC3 s hs r' c' hF')
            have h3 : Tendsto (fun s => optValue3 (famModel θ σ s) p) (𝓝[>] 0) (𝓝 U) := by
              rw [tendsto_order]; constructor
              · intro a ha
                filter_upwards [hlow (U - a) (by linarith only [ha]), hIoo] with s ⟨r, c, hF, hπ⟩ hs
                refine lt_of_lt_of_le (by linarith only [hπ]) (le_csSup ⟨U, ?_⟩ ⟨r, c, hRC3 s hs r c hF, rfl⟩)
                rintro _ ⟨r', c', hF', rfl⟩; exact hup3 s hs r' c' hF'
              · intro a ha
                filter_upwards [hlow 1 one_pos, hIoo] with s ⟨r, c, hF, hπ⟩ hs
                refine lt_of_le_of_lt (csSup_le ⟨_, r, c, hRC3 s hs r c hF, rfl⟩ ?_) ha
                rintro _ ⟨r', c', hF', rfl⟩; exact hup3 s hs r' c' hF'
            have := hRC.div h3 hUpos.ne'
            rwa [div_self hUpos.ne'] at this
