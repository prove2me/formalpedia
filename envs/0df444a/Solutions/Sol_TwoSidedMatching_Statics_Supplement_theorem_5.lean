-- Prove2me | solution 1 for TwoSidedMatching.Statics.Supplement.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:18:43.026599+00:00
-- url     : https://prove2.me/submissions/b2c5bacc-487e-4451-9bea-5a51bf3c56f7

import Mathlib
import Definitions.Def_TwoSidedMatching_Statics_Supplement_Scale

open TwoSidedMatching
open TwoSidedMatching.Statics
open TwoSidedMatching.Statics.Supplement

/-- Theorem 5 (corrected): all eight comparisons, no continuity premise.
Only the buyer-family volume and seller-price comparisons require nonnegative
fixed-side costs; buyer price and optimized profit retain the unrestricted domain. -/
theorem solution (lamD lamS T : ℝ)
    (hD : 0 < lamD) (hS : 0 < lamS) (hT : 0 < T) :
    (∀ M : ℝ → ScaleMarket,
      BuyerScaleFamily M → (∀ θ : ℝ, 0 < θ → (M θ).Regular ∧ BuyerIGFR (M θ).buyer) →
      ∀ θ₁ θ₂ : ℝ, 0 < θ₁ → θ₁ ≤ θ₂ →
        scaleP (M θ₁) lamD lamS T ≤ scaleP (M θ₂) lamD lamS T ∧
        scaleValue (M θ₁) lamD lamS T ≤ scaleValue (M θ₂) lamD lamS T ∧
        (0 ≤ (M 1).seller.lo →
          scaleW (M θ₁) lamD lamS T ≤ scaleW (M θ₂) lamD lamS T ∧
          scaleMu (M θ₁) lamD lamS T ≤ scaleMu (M θ₂) lamD lamS T)) ∧
    (∀ M : ℝ → ScaleMarket,
      SellerScaleFamily M → (∀ θ : ℝ, 0 < θ → (M θ).Regular ∧ SellerDGRFR (M θ).seller) →
      ∀ θ₁ θ₂ : ℝ, 0 < θ₁ → θ₁ ≤ θ₂ →
        scaleP (M θ₁) lamD lamS T ≤ scaleP (M θ₂) lamD lamS T ∧
        scaleW (M θ₁) lamD lamS T ≤ scaleW (M θ₂) lamD lamS T ∧
        scaleMu (M θ₂) lamD lamS T ≤ scaleMu (M θ₁) lamD lamS T ∧
        scaleValue (M θ₂) lamD lamS T ≤ scaleValue (M θ₁) lamD lamS T) ∧
    (∀ E : TwoSidedMatching.Statics.Environment, E.Regular → 0 ≤ E.loS →
      ∃ M : ScaleMarket, RepresentsEnvironment M E ∧
        scaleMu M lamD lamS T = TwoSidedMatching.Statics.muStar E lamD lamS T ∧
        scaleP M lamD lamS T = (TwoSidedMatching.Statics.pStar E lamD lamS T : EReal) ∧
        scaleW M lamD lamS T = (TwoSidedMatching.Statics.wStar E lamD lamS T : EReal) ∧
        scaleValue M lamD lamS T = (TwoSidedMatching.Statics.fluidValue E lamD lamS T : EReal)) := by
          have hBuyerValue : ∀ M : ℝ → ScaleMarket,
              BuyerScaleFamily M → ∀ θ₁ θ₂ : ℝ, 0 < θ₁ → θ₁ ≤ θ₂ →
                scaleValue (M θ₁) lamD lamS T ≤ scaleValue (M θ₂) lamD lamS T := by
            have hcdf_le : ∀ (D : ScaleDistribution) (x : ℝ), scaleCDF D x ≤ 1 := by
              intro D x
              haveI := D.probability
              exact ProbabilityTheory.cdf_le_one D.law x
            have hcdf_nn : ∀ (D : ScaleDistribution) (x : ℝ), 0 ≤ scaleCDF D x := by
              intro D x
              haveI := D.probability
              exact ProbabilityTheory.cdf_nonneg D.law x
            intro M hM θ₁ θ₂ h1 h12
            have h2 : 0 < θ₂ := lt_of_lt_of_le h1 h12
            obtain ⟨-, -, hc1, hs1⟩ := hM θ₁ h1
            obtain ⟨-, -, hc2, hs2⟩ := hM θ₂ h2
            set r := θ₂ / θ₁ with hr
            have hr1 : 1 ≤ r := by rw [hr, le_div_iff₀ h1]; linarith
            have hsurv : ∀ p : ℝ, scaleSurvival (M θ₂).buyer (r * p) = scaleSurvival (M θ₁).buyer p := by
              intro p
              unfold scaleSurvival
              have e1 := hc1 (p / θ₁)
              have e2 := hc2 (p / θ₁)
              have : θ₂ * (p / θ₁) = r * p := by rw [hr]; field_simp
              have h' : θ₁ * (p / θ₁) = p := by field_simp
              rw [this] at e2; rw [h'] at e1; rw [e1, e2]
            have hseller : (M θ₂).seller = (M θ₁).seller := by rw [hs1, hs2]
            apply sSup_le
            rintro z ⟨π, ⟨hmeas, hpt, hi1, hi2⟩, rfl⟩
            set π' : ℝ → ℝ × ℝ := fun t => (r * (π t).1, (π t).2) with hπ'
            have hfeas : ScaleFeasible (M θ₂) lamD lamS T π' := by
              refine ⟨?_, ?_, ?_, ?_⟩
              · exact (measurable_const.mul hmeas.fst).prodMk hmeas.snd
              · intro t ht
                obtain ⟨a, b, c⟩ := hpt t ht
                refine ⟨by simp only [hπ']; positivity, b, ?_⟩
                simp only [hπ', hsurv, hseller]; exact c
              · have : (fun t => lamD * (π' t).1 * scaleSurvival (M θ₂).buyer (π' t).1) =
                    fun t => r * (lamD * (π t).1 * scaleSurvival (M θ₁).buyer (π t).1) := by
                  funext t; simp only [hπ', hsurv]; ring
                rw [this]; exact hi1.const_mul r
              · simp only [hπ', hseller]; exact hi2
            refine le_trans ?_ (le_sSup ⟨π', hfeas, rfl⟩)
            rw [EReal.coe_le_coe_iff]
            unfold scaleObjective
            have e : (fun t => lamD * (π' t).1 * scaleSurvival (M θ₂).buyer (π' t).1) =
                fun t => r * (lamD * (π t).1 * scaleSurvival (M θ₁).buyer (π t).1) := by
              funext t; simp only [hπ', hsurv]; ring
            rw [e, intervalIntegral.integral_const_mul]
            simp only [hπ', hseller]
            have hnn : 0 ≤ ∫ t in (0:ℝ)..T, lamD * (π t).1 * scaleSurvival (M θ₁).buyer (π t).1 := by
              apply intervalIntegral.integral_nonneg hT.le
              intro t ht
              have := (hpt t ht).1
              have : 0 ≤ scaleSurvival (M θ₁).buyer (π t).1 := by
                unfold scaleSurvival; linarith [hcdf_le (M θ₁).buyer (π t).1]
              positivity
            linarith only [le_mul_of_one_le_left hnn hr1]
          have hSellerValue : ∀ M : ℝ → ScaleMarket,
              SellerScaleFamily M → ∀ θ₁ θ₂ : ℝ, 0 < θ₁ → θ₁ ≤ θ₂ →
                scaleValue (M θ₂) lamD lamS T ≤ scaleValue (M θ₁) lamD lamS T := by
            have hcdf_nn : ∀ (D : ScaleDistribution) (x : ℝ), 0 ≤ scaleCDF D x := by
              intro D x
              have := D.probability
              exact ProbabilityTheory.cdf_nonneg D.law x
            intro M hM θ₁ θ₂ h1 h12
            have h2 : 0 < θ₂ := lt_of_lt_of_le h1 h12
            obtain ⟨-, -, hc1, hs1⟩ := hM θ₁ h1
            obtain ⟨-, -, hc2, hs2⟩ := hM θ₂ h2
            set r := θ₁ / θ₂ with hr
            have hr0 : 0 ≤ r := by positivity
            have hr1 : r ≤ 1 := by rw [hr, div_le_iff₀ h2]; linarith
            have hcdf : ∀ w : ℝ, scaleCDF (M θ₁).seller (r * w) = scaleCDF (M θ₂).seller w := by
              intro w
              have e1 := hc1 (w / θ₂)
              have e2 := hc2 (w / θ₂)
              have : θ₁ * (w / θ₂) = r * w := by rw [hr]; field_simp
              have h' : θ₂ * (w / θ₂) = w := by field_simp
              rw [this] at e1; rw [h'] at e2; rw [e1, e2]
            have hbuyer : (M θ₁).buyer = (M θ₂).buyer := by rw [hs1, hs2]
            apply sSup_le
            rintro z ⟨π, ⟨hmeas, hpt, hi1, hi2⟩, rfl⟩
            set π' : ℝ → ℝ × ℝ := fun t => ((π t).1, r * (π t).2) with hπ'
            have e : (fun t => lamS * (π' t).2 * scaleCDF (M θ₁).seller (π' t).2) =
                fun t => r * (lamS * (π t).2 * scaleCDF (M θ₂).seller (π t).2) := by
              funext t; simp only [hπ', hcdf]; ring
            have hfeas : ScaleFeasible (M θ₁) lamD lamS T π' := by
              refine ⟨?_, ?_, ?_, ?_⟩
              · exact hmeas.fst.prodMk (measurable_const.mul hmeas.snd)
              · intro t ht
                obtain ⟨a, b, c⟩ := hpt t ht
                refine ⟨a, by simp only [hπ']; positivity, ?_⟩
                simp only [hπ', hcdf, hbuyer]; exact c
              · simp only [hπ', hbuyer]; exact hi1
              · rw [e]; exact hi2.const_mul r
            refine le_trans ?_ (le_sSup ⟨π', hfeas, rfl⟩)
            rw [EReal.coe_le_coe_iff]
            unfold scaleObjective
            rw [e, intervalIntegral.integral_const_mul]
            simp only [hπ', hbuyer]
            have hnn : 0 ≤ ∫ t in (0:ℝ)..T, lamS * (π t).2 * scaleCDF (M θ₂).seller (π t).2 := by
              apply intervalIntegral.integral_nonneg hT.le
              intro t ht
              have := (hpt t ht).2.1
              have := hcdf_nn (M θ₂).seller (π t).2
              positivity
            linarith only [mul_le_of_le_one_left hnn hr1]
          have hdivmono : ∀ (c a b : ℝ), 0 < c → a ≤ b → a / c ≤ b / c :=
            fun c a b hc h => div_le_div_of_nonneg_right h hc.le
          have hmono : ∀ D : ScaleDistribution, Monotone (scaleCDF D) :=
            fun D a b hab => (ProbabilityTheory.cdf D.law).mono hab
          have hnn : ∀ (D : ScaleDistribution) (x : ℝ), 0 ≤ scaleCDF D x := by
            intro D x
            have := D.probability
            exact ProbabilityTheory.cdf_nonneg D.law x
          have hsupp : ∀ (D : ScaleDistribution) (x : ℝ), (0 < scaleCDF D x ∧ scaleCDF D x < 1) ↔
              D.lo < (x : EReal) ∧ (x : EReal) < D.hi := fun D x => D.support x
          have hIoc : ∀ (D : ScaleDistribution) (a b : ℝ),
              D.law (Set.Ioc a b) = ENNReal.ofReal (scaleCDF D b - scaleCDF D a) := by
            intro D a b
            have := D.probability
            conv_lhs => rw [← ProbabilityTheory.measure_cdf D.law]
            rw [StieltjesFunction.measure_Ioc]
            rfl
          have hstrict0 : ∀ (D : ScaleDistribution) (a b : ℝ), a < b → D.lo < (a : EReal) → (b : EReal) < D.hi →
              scaleCDF D a < scaleCDF D b := by
            intro D a b hab ha hb
            by_contra hc
            push Not at hc
            have h0 : D.law (Set.Ioc a b) = 0 := by
              rw [hIoc]; exact ENNReal.ofReal_eq_zero.2 (by linarith)
            rw [D.density, MeasureTheory.withDensity_apply _ measurableSet_Ioc,
              MeasureTheory.lintegral_eq_zero_iff (D.measurable_pdf.ennreal_ofReal)] at h0
            have h1 : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.Ioc a b)), False := by
              filter_upwards [h0, MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx hxm
              have hp := D.positive x (ha.trans (EReal.coe_lt_coe_iff.2 hxm.1))
                (lt_of_le_of_lt (EReal.coe_le_coe_iff.2 hxm.2) hb)
              have : ENNReal.ofReal (D.pdf x) = 0 := hx
              rw [ENNReal.ofReal_eq_zero] at this
              linarith
            rw [Filter.eventually_false_iff_eq_bot, MeasureTheory.ae_eq_bot, MeasureTheory.Measure.restrict_eq_zero,
              Real.volume_Ioc, ENNReal.ofReal_eq_zero] at h1
            linarith
          -- strict monotonicity to the left / right of an interior point
          have hstrictL : ∀ (D : ScaleDistribution) (a b : ℝ), a < b → D.lo < (b : EReal) → (b : EReal) < D.hi →
              scaleCDF D a < scaleCDF D b := by
            intro D a b hab hl hb
            obtain ⟨c, hc1, hc2⟩ := EReal.lt_iff_exists_real_btwn.1
              (max_lt hl (EReal.coe_lt_coe_iff.2 hab))
            have hca : a < c := EReal.coe_lt_coe_iff.1 (lt_of_le_of_lt (le_max_right _ _) hc1)
            exact lt_of_le_of_lt (hmono D hca.le) (hstrict0 D c b (EReal.coe_lt_coe_iff.1 hc2)
              (lt_of_le_of_lt (le_max_left _ _) hc1) hb)
          have hstrictR : ∀ (D : ScaleDistribution) (a b : ℝ), a < b → D.lo < (a : EReal) → (a : EReal) < D.hi →
              scaleCDF D a < scaleCDF D b := by
            intro D a b hab hl hb
            obtain ⟨c, hc1, hc2⟩ := EReal.lt_iff_exists_real_btwn.1
              (lt_min hb (EReal.coe_lt_coe_iff.2 hab))
            have hcb : c < b := EReal.coe_lt_coe_iff.1 (lt_of_lt_of_le hc2 (min_le_right _ _))
            exact lt_of_lt_of_le (hstrict0 D a c (EReal.coe_lt_coe_iff.1 hc1) hl
              (lt_of_lt_of_le hc2 (min_le_left _ _))) (hmono D hcb.le)
          have hcont : ∀ D : ScaleDistribution, Continuous (scaleCDF D) := by
            intro D
            have hP := D.probability
            rw [continuous_iff_continuousAt]
            intro x
            have hs : D.law {x} = 0 := by
              rw [D.density]
              exact MeasureTheory.withDensity_absolutelyContinuous _ _ (by simp)
            rw [← ProbabilityTheory.measure_cdf D.law, StieltjesFunction.measure_singleton,
              ENNReal.ofReal_eq_zero] at hs
            rw [(hmono D).continuousAt_iff_leftLim_eq_rightLim]
            apply le_antisymm ((hmono D).leftLim_le_rightLim le_rfl)
            have h2 : Function.rightLim (scaleCDF D) x = scaleCDF D x := (ProbabilityTheory.cdf D.law).rightLim_eq x
            rw [h2]
            have h3 : scaleCDF D x - Function.leftLim (scaleCDF D) x ≤ 0 := hs
            linarith
          have hQF : ∀ (D : ScaleDistribution) (x : ℝ), 0 < scaleCDF D x → scaleCDF D x < 1 →
              scaleQuantile D (scaleCDF D x) = x := by
            intro D x h0 h1
            have hx := (hsupp D x).1 ⟨h0, h1⟩
            unfold scaleQuantile
            apply IsLeast.csInf_eq
            refine ⟨le_refl (scaleCDF D x), ?_⟩
            intro y hy
            by_contra hc
            push Not at hc
            have h := hstrictL D y x hc hx.1 hx.2
            have : scaleCDF D x ≤ scaleCDF D y := hy
            linarith
          have hFQ : ∀ (D : ScaleDistribution) (s : ℝ), 0 < s → s < 1 → scaleCDF D (scaleQuantile D s) = s := by
            intro D s h0 h1
            have hP := D.probability
            have hbot : Filter.Tendsto (scaleCDF D) Filter.atBot (nhds 0) := ProbabilityTheory.tendsto_cdf_atBot D.law
            have htop : Filter.Tendsto (scaleCDF D) Filter.atTop (nhds 1) := ProbabilityTheory.tendsto_cdf_atTop D.law
            obtain ⟨a, ha⟩ := (hbot.eventually (gt_mem_nhds h0)).exists
            obtain ⟨b, hb⟩ := (htop.eventually (lt_mem_nhds h1)).exists
            obtain ⟨x, hx⟩ := mem_range_of_exists_le_of_exists_ge (hcont D) ⟨a, le_of_lt ha⟩ ⟨b, le_of_lt hb⟩
            have hx' : scaleCDF D x = s := hx
            rw [← hx', hQF D x (by linarith) (by linarith)]
          have hQint : ∀ (D : ScaleDistribution) (s : ℝ), 0 < s → s < 1 →
              D.lo < (scaleQuantile D s : EReal) ∧ (scaleQuantile D s : EReal) < D.hi := by
            intro D s h0 h1
            rw [← hsupp, hFQ D s h0 h1]; exact ⟨h0, h1⟩
          have hQlt : ∀ (D : ScaleDistribution) (s x : ℝ), 0 < s → s < 1 → scaleQuantile D s < x → s < scaleCDF D x := by
            intro D s x h0 h1 hx
            have := hstrictR D _ x hx (hQint D s h0 h1).1 (hQint D s h0 h1).2
            rwa [hFQ D s h0 h1] at this
          have hltQ : ∀ (D : ScaleDistribution) (s x : ℝ), 0 < s → s < 1 → x < scaleQuantile D s → scaleCDF D x < s := by
            intro D s x h0 h1 hx
            have := hstrictL D x _ hx (hQint D s h0 h1).1 (hQint D s h0 h1).2
            rwa [hFQ D s h0 h1] at this
          have hQmono : ∀ (D : ScaleDistribution) (s t : ℝ), 0 < s → s ≤ t → t < 1 → scaleQuantile D s ≤ scaleQuantile D t := by
            intro D s t h0 hst h1
            by_contra hc
            push Not at hc
            have := hQlt D t _ (by linarith) h1 hc
            rw [hFQ D s h0 (by linarith)] at this
            linarith
          -- extended quantile comparisons
          have hSQlt : ∀ (D : ScaleDistribution) (q x : ℝ), D.lo < (x : EReal) → (x : EReal) < D.hi →
              scaleSellerQuantile D q < (x : EReal) → q < scaleCDF D x := by
            intro D q x hl hh hx
            have hi := (hsupp D x).2 ⟨hl, hh⟩
            unfold scaleSellerQuantile at hx
            split_ifs at hx with a b
            · linarith [hi.1]
            · exact absurd (hx.trans hh) (lt_irrefl _)
            · exact hQlt D q x (by linarith) (by linarith) (EReal.coe_lt_coe_iff.1 hx)
          have hltSQ : ∀ (D : ScaleDistribution) (q x : ℝ), D.lo < (x : EReal) → (x : EReal) < D.hi →
              (x : EReal) < scaleSellerQuantile D q → scaleCDF D x < q := by
            intro D q x hl hh hx
            have hi := (hsupp D x).2 ⟨hl, hh⟩
            unfold scaleSellerQuantile at hx
            split_ifs at hx with a b
            · exact absurd (hx.trans hl) (lt_irrefl _)
            · linarith [hi.2]
            · exact hltQ D q x (by linarith) (by linarith) (EReal.coe_lt_coe_iff.1 hx)
          have hSQlo : ∀ (D : ScaleDistribution) (q : ℝ), D.lo ≤ scaleSellerQuantile D q := by
            intro D q
            unfold scaleSellerQuantile
            split_ifs with a b
            · exact le_rfl
            · exact D.lo_lt_hi.le
            · exact (hQint D q (by linarith) (by linarith)).1.le
          have hSQhi : ∀ (D : ScaleDistribution) (q : ℝ), scaleSellerQuantile D q ≤ D.hi := by
            intro D q
            unfold scaleSellerQuantile
            split_ifs with a b
            · exact D.lo_lt_hi.le
            · exact le_rfl
            · exact (hQint D q (by linarith) (by linarith)).2.le
          have hSQ : ∀ (D : ScaleDistribution) (q₁ q₂ : ℝ), q₁ ≤ q₂ →
              scaleSellerQuantile D q₁ ≤ scaleSellerQuantile D q₂ := by
            intro D q₁ q₂ h12
            by_cases a : q₁ ≤ 0
            · have : scaleSellerQuantile D q₁ = D.lo := if_pos a
              rw [this]; exact hSQlo D q₂
            by_cases b : 1 ≤ q₂
            · have : scaleSellerQuantile D q₂ = D.hi := by
                unfold scaleSellerQuantile
                rw [if_neg (by linarith), if_pos b]
              rw [this]; exact hSQhi D q₁
            push Not at a b
            unfold scaleSellerQuantile
            rw [if_neg (by linarith), if_neg (by linarith), if_neg (by linarith), if_neg (by linarith)]
            exact EReal.coe_le_coe_iff.2 (hQmono D _ _ a h12 b)
          have hBS : ∀ (D : ScaleDistribution) (q : ℝ),
              scaleBuyerQuantile D q = scaleSellerQuantile D (1 - q) := by
            intro D q
            unfold scaleBuyerQuantile scaleSellerQuantile
            split_ifs <;> first | rfl | (exfalso; linarith)
          have hBQ : ∀ (D : ScaleDistribution) (q₁ q₂ : ℝ), q₁ ≤ q₂ →
              scaleBuyerQuantile D q₂ ≤ scaleBuyerQuantile D q₁ := by
            intro D q₁ q₂ h
            rw [hBS, hBS]; exact hSQ D _ _ (by linarith only [h])
          -- pointwise density scaling on a dense set
          have hdens : ∀ (D E : ScaleDistribution) (r : ℝ), 0 < r →
              (∀ v : ℝ, scaleCDF E (r * v) = scaleCDF D v) →
              Dense {x : ℝ | r * E.pdf x = D.pdf (x / r)} := by
            intro D E r hr h
            have hPD := D.probability
            have hPE := E.probability
            have hm : Measurable (fun y : ℝ => r * y) := measurable_const.mul measurable_id
            have hdm : Measurable (fun x : ℝ => D.pdf (x / r) / r) :=
              (D.measurable_pdf.comp (measurable_id.div_const r)).div_const r
            have hmap : E.law = D.law.map (fun y : ℝ => r * y) := by
              have : MeasureTheory.IsProbabilityMeasure (D.law.map (fun y : ℝ => r * y)) :=
                MeasureTheory.Measure.isProbabilityMeasure_map hm.aemeasurable
              apply MeasureTheory.Measure.ext_of_Iic
              intro a
              rw [MeasureTheory.Measure.map_apply hm measurableSet_Iic]
              have hpre : (fun y : ℝ => r * y) ⁻¹' Set.Iic a = Set.Iic (a / r) := by
                ext y; simp only [Set.mem_preimage, Set.mem_Iic]; rw [le_div_iff₀ hr, mul_comm]
              rw [hpre]
              have h1 := h (a / r)
              rw [mul_div_cancel₀ a hr.ne'] at h1
              unfold scaleCDF at h1
              rw [ProbabilityTheory.cdf_eq_real, ProbabilityTheory.cdf_eq_real] at h1
              exact (MeasureTheory.measureReal_eq_measureReal_iff).1 h1
            have hden : MeasureTheory.volume.withDensity (fun x => ENNReal.ofReal (E.pdf x)) =
                MeasureTheory.volume.withDensity (fun x => ENNReal.ofReal (D.pdf (x / r) / r)) := by
              rw [← E.density, hmap]
              ext s hs
              rw [MeasureTheory.Measure.map_apply hm hs, D.density,
                MeasureTheory.withDensity_apply _ (hm hs), MeasureTheory.withDensity_apply _ hs]
              conv_rhs => rw [← Real.smul_map_volume_mul_left hr.ne']
              rw [MeasureTheory.Measure.restrict_smul, MeasureTheory.lintegral_smul_measure,
                MeasureTheory.setLIntegral_map hs hdm.ennreal_ofReal hm, abs_of_pos hr, smul_eq_mul,
                ← MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
              congr 1
              ext y
              rw [← ENNReal.ofReal_mul hr.le]
              congr 1
              rw [mul_div_cancel_left₀ y hr.ne']
              field_simp
            have hae := (MeasureTheory.withDensity_eq_iff_of_sigmaFinite
              E.measurable_pdf.ennreal_ofReal.aemeasurable hdm.ennreal_ofReal.aemeasurable).1 hden
            apply MeasureTheory.Measure.dense_of_ae (μ := MeasureTheory.volume)
            filter_upwards [hae] with x hx
            have h2 := (ENNReal.ofReal_eq_ofReal_iff (E.nonneg x) (div_nonneg (D.nonneg _) hr.le)).1 hx
            rw [h2]; field_simp
          have hLT : 0 < lamD * T := by positivity
          have hLS : 0 < lamS * T := by positivity
          have hVanti : ∀ M : ScaleMarket, M.Regular → ∀ μ₁ μ₂, 0 < μ₁ → μ₁ ≤ μ₂ → μ₂ < min (lamD * T) (lamS * T) →
              scaleV M lamD lamS T μ₂ ≤ scaleV M lamD lamS T μ₁ := by
            intro M hM μ₁ μ₂ h0 h12 h2
            have hd := lt_of_lt_of_le h2 (min_le_left _ _)
            have hs := lt_of_lt_of_le h2 (min_le_right _ _)
            have q0 : 0 < μ₁ / (lamD * T) := by positivity
            have q12 : μ₁ / (lamD * T) ≤ μ₂ / (lamD * T) := div_le_div_of_nonneg_right h12 hLT.le
            have q1 : μ₂ / (lamD * T) < 1 := by rwa [div_lt_one hLT]
            have s0 : 0 < μ₁ / (lamS * T) := by positivity
            have s12 : μ₁ / (lamS * T) ≤ μ₂ / (lamS * T) := div_le_div_of_nonneg_right h12 hLS.le
            have s1 : μ₂ / (lamS * T) < 1 := by rwa [div_lt_one hLS]
            unfold scaleV
            have a := hM.1 (hQint M.buyer (1 - μ₂ / (lamD * T)) (by linarith) (by linarith))
              (hQint M.buyer (1 - μ₁ / (lamD * T)) (by linarith) (by linarith))
              (hQmono M.buyer _ _ (by linarith) (by linarith) (by linarith))
            have b := hM.2 (hQint M.seller (μ₁ / (lamS * T)) (by linarith) (by linarith))
              (hQint M.seller (μ₂ / (lamS * T)) (by linarith) (by linarith))
              (hQmono M.seller _ _ (by linarith) (by linarith) (by linarith))
            linarith
          have hm0 : 0 < min (lamD * T) (lamS * T) := lt_min hLT hLS
          have hbdd : ∀ M : ScaleMarket, BddAbove ({0} ∪ {μ | μ ∈ Set.Ioo 0 (min (lamD * T) (lamS * T)) ∧
              0 ≤ scaleV M lamD lamS T μ}) := by
            intro M
            refine ⟨min (lamD * T) (lamS * T), ?_⟩
            rintro x (hx | hx)
            · rw [Set.mem_singleton_iff.1 hx]; exact hm0.le
            · exact hx.1.2.le
          have hmu0 : ∀ M : ScaleMarket, 0 ≤ scaleMu M lamD lamS T :=
            fun M => le_csSup (hbdd M) (Set.mem_union_left _ rfl)
          have hmum : ∀ M : ScaleMarket, scaleMu M lamD lamS T ≤ min (lamD * T) (lamS * T) := by
            intro M
            apply csSup_le (Set.nonempty_of_mem (Set.mem_union_left _ (Set.mem_singleton (0:ℝ))))
            rintro x (hx | hx)
            · rw [Set.mem_singleton_iff.1 hx]; exact hm0.le
            · exact hx.1.2.le
          have hAbove : ∀ (M : ScaleMarket) (μ : ℝ), scaleMu M lamD lamS T < μ → μ < min (lamD * T) (lamS * T) →
              scaleV M lamD lamS T μ < 0 := by
            intro M μ h1 h2
            by_contra hc
            push Not at hc
            have := le_csSup (hbdd M) (Set.mem_union_right _ ⟨⟨lt_of_le_of_lt (hmu0 M) h1, h2⟩, hc⟩)
            exact absurd h1 (not_lt.2 this)
          have hBelow : ∀ (M : ScaleMarket), M.Regular → ∀ (μ : ℝ), 0 < μ → μ < scaleMu M lamD lamS T →
              0 ≤ scaleV M lamD lamS T μ := by
            intro M hM μ h0 h1
            obtain ⟨x, hx, hμx⟩ := exists_lt_of_lt_csSup (Set.nonempty_of_mem (Set.mem_union_left _ (Set.mem_singleton (0:ℝ)))) h1
            rcases hx with hx | hx
            · rw [Set.mem_singleton_iff.1 hx] at hμx; linarith
            · exact hx.2.trans (hVanti M hM μ x h0 hμx.le hx.1.2)
          have hVB : ∀ (M : ScaleMarket) (p : ℝ), 0 < scaleCDF M.buyer p → scaleCDF M.buyer p < 1 →
              scaleV M lamD lamS T (lamD * T * scaleSurvival M.buyer p) = scaleVirtualB M.buyer p -
                scaleVirtualS M.seller (scaleQuantile M.seller (lamD * T * scaleSurvival M.buyer p / (lamS * T))) := by
            intro M p h0 h1
            unfold scaleV
            rw [mul_div_cancel_left₀ _ hLT.ne']
            have : 1 - scaleSurvival M.buyer p = scaleCDF M.buyer p := by unfold scaleSurvival; ring
            rw [this, hQF _ _ h0 h1]
          have hVS : ∀ (M : ScaleMarket) (w : ℝ), 0 < scaleCDF M.seller w → scaleCDF M.seller w < 1 →
              scaleV M lamD lamS T (lamS * T * scaleCDF M.seller w) =
                scaleVirtualB M.buyer (scaleQuantile M.buyer (1 - lamS * T * scaleCDF M.seller w / (lamD * T))) -
                scaleVirtualS M.seller w := by
            intro M w h0 h1
            unfold scaleV
            rw [mul_div_cancel_left₀ _ hLS.ne', hQF _ _ h0 h1]
          have hdivlt : ∀ (a b c : ℝ), 0 < c → a < b / c → c * a < b := by
            intro a b c hc h; rw [lt_div_iff₀ hc] at h; linarith
          have hltdiv : ∀ (a b c : ℝ), 0 < c → b / c < a → b < c * a := by
            intro a b c hc h; rw [div_lt_iff₀ hc] at h; linarith
          refine ⟨?_, ?_, ?_⟩
          · intro M hM hreg θ₁ θ₂ h1 h12
            have h2 : 0 < θ₂ := lt_of_lt_of_le h1 h12
            have hsel : (M θ₂).seller = (M θ₁).seller := by
              rw [(hM θ₁ h1).2.2.2, (hM θ₂ h2).2.2.2]
            have hr0 : 0 < θ₂ / θ₁ := div_pos h2 h1
            have hr1 : 1 ≤ θ₂ / θ₁ := by rw [le_div_iff₀ h1]; linarith
            have hcdf : ∀ v : ℝ, scaleCDF (M θ₂).buyer (θ₂ / θ₁ * v) = scaleCDF (M θ₁).buyer v := by
              intro v
              have e1 := (hM θ₁ h1).2.2.1 (v / θ₁)
              have e2 := (hM θ₂ h2).2.2.1 (v / θ₁)
              rw [mul_div_cancel₀ v h1.ne'] at e1
              have : θ₂ * (v / θ₁) = θ₂ / θ₁ * v := by ring
              rw [this] at e2
              rw [e1, e2]
            have hlo1 : (M θ₁).buyer.lo = 0 := (hM θ₁ h1).1
            have hlo2 : (M θ₂).buyer.lo = 0 := (hM θ₂ h2).1
            have hD12 := hdens _ _ _ hr0 hcdf
            generalize θ₂ / θ₁ = r at hr0 hr1 hcdf hD12
            have hcdf' : ∀ x : ℝ, scaleCDF (M θ₂).buyer x = scaleCDF (M θ₁).buyer (x / r) := by
              intro x; rw [← hcdf, mul_div_cancel₀ x hr0.ne']
            obtain ⟨hR1, hI1⟩ := hreg θ₁ h1
            obtain ⟨hR2, hI2⟩ := hreg θ₂ h2
            refine ⟨?_, hBuyerValue M hM θ₁ θ₂ h1 h12, ?_⟩
            · --
              by_contra hc
              push Not at hc
              obtain ⟨a, ha1, ha2⟩ := EReal.lt_iff_exists_real_btwn.1 hc
              obtain ⟨b, hb1, hb2⟩ := EReal.lt_iff_exists_real_btwn.1 ha2
              obtain ⟨p, hgood, hap, hpb⟩ := hD12.exists_between (EReal.coe_lt_coe_iff.1 hb1)
              have hp2 : scaleP (M θ₂) lamD lamS T < (p : EReal) := ha1.trans (EReal.coe_lt_coe_iff.2 hap)
              have hp1 : (p : EReal) < scaleP (M θ₁) lamD lamS T := (EReal.coe_lt_coe_iff.2 hpb).trans hb2
              unfold scaleP at hp1 hp2
              rw [hBS] at hp1 hp2
              have hp0' : (0 : EReal) < (p : EReal) := by
                have := hSQlo (M θ₂).buyer (1 - scaleMu (M θ₂) lamD lamS T / (lamD * T))
                rw [hlo2] at this
                exact lt_of_le_of_lt this hp2
              have hp0 : 0 < p := EReal.coe_pos.1 hp0'
              have hl1 : (M θ₁).buyer.lo < (p : EReal) := by rw [hlo1]; exact hp0'
              have hh1 : (p : EReal) < (M θ₁).buyer.hi := lt_of_lt_of_le hp1 (hSQhi _ _)
              have hprle : p / r ≤ p := div_le_self hp0.le hr1
              have hl1' : (M θ₁).buyer.lo < ((p / r : ℝ) : EReal) := by
                rw [hlo1]; exact EReal.coe_pos.2 (div_pos hp0 hr0)
              have hh1' : ((p / r : ℝ) : EReal) < (M θ₁).buyer.hi :=
                lt_of_le_of_lt (EReal.coe_le_coe_iff.2 hprle) hh1
              have hF1 := (hsupp _ _).2 ⟨hl1, hh1⟩
              have hF1' := (hsupp _ _).2 ⟨hl1', hh1'⟩
              have hF2 := hF1'
              rw [← hcdf'] at hF2
              have hi2 := (hsupp _ _).1 hF2
              have hq1 := hltSQ _ _ _ hl1 hh1 hp1
              have hq2 := hSQlt _ _ _ hi2.1 hi2.2 hp2
              have hFle : scaleCDF (M θ₂).buyer p ≤ scaleCDF (M θ₁).buyer p := by
                rw [hcdf']; exact hmono _ hprle
              have hμ1 : scaleMu (M θ₁) lamD lamS T < lamD * T * scaleSurvival (M θ₁).buyer p := by
                apply hltdiv _ _ _ hLT; unfold scaleSurvival; linarith
              have hμ2 : lamD * T * scaleSurvival (M θ₂).buyer p < scaleMu (M θ₂) lamD lamS T := by
                apply hdivlt _ _ _ hLT; unfold scaleSurvival; linarith
              have hμ12 : lamD * T * scaleSurvival (M θ₁).buyer p ≤ lamD * T * scaleSurvival (M θ₂).buyer p := by
                apply mul_le_mul_of_nonneg_left _ hLT.le; unfold scaleSurvival; linarith
              have hS1 : 0 < scaleSurvival (M θ₁).buyer p := by unfold scaleSurvival; linarith [hF1.2]
              have hS2 : 0 < scaleSurvival (M θ₂).buyer p := by unfold scaleSurvival; linarith [hF2.2]
              have hm2 := lt_of_lt_of_le hμ2 (hmum (M θ₂))
              have hV1 := hAbove _ _ hμ1 (lt_of_le_of_lt hμ12 hm2)
              have hV2 := hBelow _ hR2 _ (mul_pos hLT hS2) hμ2
              rw [hVB _ _ hF1.1 hF1.2] at hV1
              rw [hVB _ _ hF2.1 hF2.2, hsel] at hV2
              have hm2s := lt_of_lt_of_le hm2 (min_le_right _ _)
              have hψ := hR1.2 (hQint (M θ₁).seller (lamD * T * scaleSurvival (M θ₁).buyer p / (lamS * T))
                  (by positivity) (by rw [div_lt_one hLS]; linarith))
                (hQint (M θ₁).seller (lamD * T * scaleSurvival (M θ₂).buyer p / (lamS * T))
                  (by positivity) (by rw [div_lt_one hLS]; linarith))
                (hQmono _ _ _ (by positivity) (hdivmono _ _ _ hLS hμ12) (by rw [div_lt_one hLS]; linarith))
              have hf1 := (M θ₁).buyer.positive p hl1 hh1
              have hf2 := (M θ₂).buyer.positive p hi2.1 hi2.2
              have hig := hI1 (show p / r ∈ {ξ | ProbabilityTheory.cdf (M θ₁).buyer.law ξ < 1} from hF1'.2)
                (show p ∈ {ξ | ProbabilityTheory.cdf (M θ₁).buyer.law ξ < 1} from hF1.2) hprle
              simp only [LariviereIGFR.Char.genFailureRate, LariviereIGFR.Char.failureRate] at hig
              rw [if_pos ⟨hl1'.le, hh1'.le⟩, if_pos ⟨hl1.le, hh1.le⟩] at hig
              have es1 : LariviereIGFR.Char.survival (M θ₁).buyer.law (p / r) = scaleSurvival (M θ₂).buyer p := by
                unfold scaleSurvival; rw [hcdf']; rfl
              have es2 : LariviereIGFR.Char.survival (M θ₁).buyer.law p = scaleSurvival (M θ₁).buyer p := rfl
              have hgood' : r * (M θ₂).buyer.pdf p = (M θ₁).buyer.pdf (p / r) := hgood
              rw [es1, es2, ← hgood'] at hig
              have hig2 : p * ((M θ₂).buyer.pdf p / scaleSurvival (M θ₂).buyer p) ≤
                  p * ((M θ₁).buyer.pdf p / scaleSurvival (M θ₁).buyer p) := by
                refine le_trans (le_of_eq ?_) hig
                field_simp
              have hig3 := le_of_mul_le_mul_left hig2 hp0
              have hig4 : scaleSurvival (M θ₁).buyer p / (M θ₁).buyer.pdf p ≤
                  scaleSurvival (M θ₂).buyer p / (M θ₂).buyer.pdf p := by
                rw [div_le_div_iff₀ hS2 hS1] at hig3
                rw [div_le_div_iff₀ hf1 hf2]
                linarith
              have hφ : scaleVirtualB (M θ₂).buyer p ≤ scaleVirtualB (M θ₁).buyer p := by
                unfold scaleVirtualB; linarith
              linarith
            intro hlo0
            have hmu : scaleMu (M θ₁) lamD lamS T ≤ scaleMu (M θ₂) lamD lamS T := by
              have hm' : (M 1).seller = (M θ₁).seller := (hM θ₁ h1).2.2.2.symm
              rw [hm'] at hlo0
              by_contra hc
              push Not at hc
              obtain ⟨μ, hμ, hμ2⟩ := exists_lt_of_lt_csSup (Set.nonempty_of_mem (Set.mem_union_left _ (Set.mem_singleton (0:ℝ)))) hc
              rcases hμ with hμ | hμ
              · rw [Set.mem_singleton_iff.1 hμ] at hμ2; linarith [hmu0 (M θ₂)]
              obtain ⟨⟨hμ0, hμm⟩, hVμ⟩ := hμ
              obtain ⟨ν, hν1, hν2⟩ := exists_between hμ2
              have hν0 : 0 < ν := lt_of_le_of_lt (hmu0 _) hν1
              have hμd := lt_of_lt_of_le hμm (min_le_left _ _)
              have hμs := lt_of_lt_of_le hμm (min_le_right _ _)
              have a1 : 0 < μ / (lamD * T) := by positivity
              have a2 : μ / (lamD * T) < 1 := by rwa [div_lt_one hLT]
              have a3 : 0 < ν / (lamD * T) := by positivity
              have a4 : ν / (lamD * T) < μ / (lamD * T) := div_lt_div_of_pos_right hν2 hLT
              have hQQ : scaleQuantile (M θ₁).buyer (1 - μ / (lamD * T)) <
                  scaleQuantile (M θ₁).buyer (1 - ν / (lamD * T)) := by
                by_contra hcc
                push Not at hcc
                have := hmono (M θ₁).buyer hcc
                rw [hFQ _ _ (by linarith) (by linarith), hFQ _ _ (by linarith) (by linarith)] at this
                linarith
              obtain ⟨x, hgood, hx1, hx2⟩ := hD12.exists_between (mul_lt_mul_of_pos_left hQQ hr0)
              have hgood' : r * (M θ₂).buyer.pdf x = (M θ₁).buyer.pdf (x / r) := hgood
              obtain ⟨p, rfl⟩ : ∃ p, x = r * p := ⟨x / r, (mul_div_cancel₀ x hr0.ne').symm⟩
              rw [mul_div_cancel_left₀ p hr0.ne'] at hgood'
              have hx1 := lt_of_mul_lt_mul_left hx1 hr0.le
              have hx2 := lt_of_mul_lt_mul_left hx2 hr0.le
              have hc1 := hQlt _ _ _ (by linarith) (by linarith) hx1
              have hc2 := hltQ _ _ _ (by linarith) (by linarith) hx2
              have hF1 : 0 < scaleCDF (M θ₁).buyer p := by linarith
              have hF2 : scaleCDF (M θ₁).buyer p < 1 := by linarith
              have hν' : ν < lamD * T * scaleSurvival (M θ₁).buyer p := by
                apply hltdiv _ _ _ hLT; unfold scaleSurvival; linarith
              have hμ' : lamD * T * scaleSurvival (M θ₁).buyer p < μ := by
                apply hdivlt _ _ _ hLT; unfold scaleSurvival; linarith
              have hSS : scaleSurvival (M θ₂).buyer (r * p) = scaleSurvival (M θ₁).buyer p := by
                unfold scaleSurvival; rw [hcdf]
              have hV2 := hAbove (M θ₂) _ (hν1.trans hν') (hμ'.trans hμm)
              have hV1 := hVμ.trans (hVanti _ hR1 _ _ (hν0.trans hν') hμ'.le hμm)
              rw [hVB _ _ hF1 hF2] at hV1
              rw [← hSS, hVB _ _ (by rw [hcdf]; exact hF1) (by rw [hcdf]; exact hF2), hSS, hsel] at hV2
              have hint := hQint (M θ₁).seller (lamD * T * scaleSurvival (M θ₁).buyer p / (lamS * T))
                (div_pos (hν0.trans hν') hLS) (by rw [div_lt_one hLS]; linarith)
              have hψ0 : 0 ≤ scaleVirtualS (M θ₁).seller
                  (scaleQuantile (M θ₁).seller (lamD * T * scaleSurvival (M θ₁).buyer p / (lamS * T))) := by
                unfold scaleVirtualS
                have b1 : 0 < scaleQuantile (M θ₁).seller (lamD * T * scaleSurvival (M θ₁).buyer p / (lamS * T)) :=
                  EReal.coe_pos.1 (lt_of_le_of_lt hlo0 hint.1)
                have b2 := div_nonneg (hnn (M θ₁).seller
                  (scaleQuantile (M θ₁).seller (lamD * T * scaleSurvival (M θ₁).buyer p / (lamS * T))))
                  ((M θ₁).seller.nonneg
                  (scaleQuantile (M θ₁).seller (lamD * T * scaleSurvival (M θ₁).buyer p / (lamS * T))))
                linarith
              have hφ : scaleVirtualB (M θ₂).buyer (r * p) = r * scaleVirtualB (M θ₁).buyer p := by
                unfold scaleVirtualB
                rw [hSS, ← hgood', mul_sub]
                congr 1
                field_simp
              rw [hφ] at hV2
              have hfin := le_mul_of_one_le_left (hψ0.trans (sub_nonneg.1 hV1)) hr1
              linarith only [hfin, hV1, hV2]
            refine ⟨?_, hmu⟩
            unfold scaleW
            rw [hsel]
            exact hSQ _ _ _ (hdivmono _ _ _ (by positivity) hmu)
          · intro M hM hreg θ₁ θ₂ h1 h12
            have h2 : 0 < θ₂ := lt_of_lt_of_le h1 h12
            have hbuy : (M θ₂).buyer = (M θ₁).buyer := by
              rw [(hM θ₁ h1).2.2.2, (hM θ₂ h2).2.2.2]
            have hr0 : 0 < θ₂ / θ₁ := div_pos h2 h1
            have hr1 : 1 ≤ θ₂ / θ₁ := by rw [le_div_iff₀ h1]; linarith
            have hcdf : ∀ v : ℝ, scaleCDF (M θ₂).seller (θ₂ / θ₁ * v) = scaleCDF (M θ₁).seller v := by
              intro v
              have e1 := (hM θ₁ h1).2.2.1 (v / θ₁)
              have e2 := (hM θ₂ h2).2.2.1 (v / θ₁)
              rw [mul_div_cancel₀ v h1.ne'] at e1
              have : θ₂ * (v / θ₁) = θ₂ / θ₁ * v := by ring
              rw [this] at e2
              rw [e1, e2]
            have hlo1 : (M θ₁).seller.lo = 0 := (hM θ₁ h1).1
            have hlo2 : (M θ₂).seller.lo = 0 := (hM θ₂ h2).1
            have hD12 := hdens _ _ _ hr0 hcdf
            generalize θ₂ / θ₁ = r at hr0 hr1 hcdf hD12
            have hcdf' : ∀ x : ℝ, scaleCDF (M θ₂).seller x = scaleCDF (M θ₁).seller (x / r) := by
              intro x; rw [← hcdf, mul_div_cancel₀ x hr0.ne']
            obtain ⟨hR1, hI1⟩ := hreg θ₁ h1
            obtain ⟨hR2, hI2⟩ := hreg θ₂ h2
            have hmu : scaleMu (M θ₂) lamD lamS T ≤ scaleMu (M θ₁) lamD lamS T := by
              by_contra hc
              push Not at hc
              obtain ⟨μ, hμ, hμ2⟩ := exists_lt_of_lt_csSup (Set.nonempty_of_mem (Set.mem_union_left _ (Set.mem_singleton (0:ℝ)))) hc
              rcases hμ with hμ | hμ
              · rw [Set.mem_singleton_iff.1 hμ] at hμ2; linarith [hmu0 (M θ₁)]
              obtain ⟨⟨hμ0, hμm⟩, hVμ⟩ := hμ
              obtain ⟨ν, hν1, hν2⟩ := exists_between hμ2
              have hν0 : 0 < ν := lt_of_le_of_lt (hmu0 _) hν1
              have hμs := lt_of_lt_of_le hμm (min_le_right _ _)
              have a1 : 0 < μ / (lamS * T) := by positivity
              have a2 : μ / (lamS * T) < 1 := by rwa [div_lt_one hLS]
              have a3 : 0 < ν / (lamS * T) := by positivity
              have a4 : ν / (lamS * T) < μ / (lamS * T) := div_lt_div_of_pos_right hν2 hLS
              have hQQ : scaleQuantile (M θ₁).seller (ν / (lamS * T)) <
                  scaleQuantile (M θ₁).seller (μ / (lamS * T)) := by
                by_contra hcc
                push Not at hcc
                have := hmono (M θ₁).seller hcc
                rw [hFQ _ _ (by linarith) (by linarith), hFQ _ _ (by linarith) (by linarith)] at this
                linarith
              obtain ⟨x, hgood, hx1, hx2⟩ := hD12.exists_between (mul_lt_mul_of_pos_left hQQ hr0)
              have hgood' : r * (M θ₂).seller.pdf x = (M θ₁).seller.pdf (x / r) := hgood
              obtain ⟨w, rfl⟩ : ∃ w, x = r * w := ⟨x / r, (mul_div_cancel₀ x hr0.ne').symm⟩
              rw [mul_div_cancel_left₀ w hr0.ne'] at hgood'
              have hx1 := lt_of_mul_lt_mul_left hx1 hr0.le
              have hx2 := lt_of_mul_lt_mul_left hx2 hr0.le
              have hc1 := hQlt _ _ _ (by linarith) (by linarith) hx1
              have hc2 := hltQ _ _ _ (by linarith) (by linarith) hx2
              have hF1 : 0 < scaleCDF (M θ₁).seller w := by linarith
              have hF2 : scaleCDF (M θ₁).seller w < 1 := by linarith
              have hν' : ν < lamS * T * scaleCDF (M θ₁).seller w := hltdiv _ _ _ hLS hc1
              have hμ' : lamS * T * scaleCDF (M θ₁).seller w < μ := hdivlt _ _ _ hLS hc2
              have hV1 := hAbove (M θ₁) _ (hν1.trans hν') (hμ'.trans hμm)
              have hV2 := hVμ.trans (hVanti _ hR2 _ _ (hν0.trans hν') hμ'.le hμm)
              rw [hVS _ _ hF1 hF2] at hV1
              rw [← hcdf, hVS _ _ (by rw [hcdf]; exact hF1) (by rw [hcdf]; exact hF2), hcdf, hbuy] at hV2
              have hw0 : 0 < w := by
                have := ((hsupp _ _).1 ⟨hF1, hF2⟩).1
                rw [hlo1] at this
                exact EReal.coe_pos.1 this
              have hψ0 : 0 ≤ scaleVirtualS (M θ₁).seller w := by
                unfold scaleVirtualS
                have b2 := div_nonneg hF1.le ((M θ₁).seller.nonneg w)
                linarith
              have hφ : scaleVirtualS (M θ₂).seller (r * w) = r * scaleVirtualS (M θ₁).seller w := by
                unfold scaleVirtualS
                rw [hcdf, ← hgood', mul_add]
                congr 1
                field_simp
              rw [hφ] at hV2
              have hfin := le_mul_of_one_le_left hψ0 hr1
              linarith only [hfin, hV1, hV2]
            refine ⟨?_, ?_, hmu, hSellerValue M hM θ₁ θ₂ h1 h12⟩
            · unfold scaleP
              rw [hbuy]
              exact hBQ _ _ _ (hdivmono _ _ _ (by positivity) hmu)
            · --
              by_contra hc
              push Not at hc
              obtain ⟨a, ha1, ha2⟩ := EReal.lt_iff_exists_real_btwn.1 hc
              obtain ⟨b, hb1, hb2⟩ := EReal.lt_iff_exists_real_btwn.1 ha2
              obtain ⟨p, hgood, hap, hpb⟩ := hD12.exists_between (EReal.coe_lt_coe_iff.1 hb1)
              have hp2 : scaleW (M θ₂) lamD lamS T < (p : EReal) := ha1.trans (EReal.coe_lt_coe_iff.2 hap)
              have hp1 : (p : EReal) < scaleW (M θ₁) lamD lamS T := (EReal.coe_lt_coe_iff.2 hpb).trans hb2
              unfold scaleW at hp1 hp2
              have hp0' : (0 : EReal) < (p : EReal) := by
                have := hSQlo (M θ₂).seller (scaleMu (M θ₂) lamD lamS T / (lamS * T))
                rw [hlo2] at this
                exact lt_of_le_of_lt this hp2
              have hp0 : 0 < p := EReal.coe_pos.1 hp0'
              have hl1 : (M θ₁).seller.lo < (p : EReal) := by rw [hlo1]; exact hp0'
              have hh1 : (p : EReal) < (M θ₁).seller.hi := lt_of_lt_of_le hp1 (hSQhi _ _)
              have hprle : p / r ≤ p := div_le_self hp0.le hr1
              have hl1' : (M θ₁).seller.lo < ((p / r : ℝ) : EReal) := by
                rw [hlo1]; exact EReal.coe_pos.2 (div_pos hp0 hr0)
              have hh1' : ((p / r : ℝ) : EReal) < (M θ₁).seller.hi :=
                lt_of_le_of_lt (EReal.coe_le_coe_iff.2 hprle) hh1
              have hF1 := (hsupp _ _).2 ⟨hl1, hh1⟩
              have hF1' := (hsupp _ _).2 ⟨hl1', hh1'⟩
              have hF2 := hF1'
              rw [← hcdf'] at hF2
              have hi2 := (hsupp _ _).1 hF2
              have hq1 := hltSQ _ _ _ hl1 hh1 hp1
              have hq2 := hSQlt _ _ _ hi2.1 hi2.2 hp2
              have hFle : scaleCDF (M θ₂).seller p ≤ scaleCDF (M θ₁).seller p := by
                rw [hcdf']; exact hmono _ hprle
              have hμ1 : lamS * T * scaleCDF (M θ₁).seller p < scaleMu (M θ₁) lamD lamS T :=
                hdivlt _ _ _ hLS hq1
              have hμ2 : scaleMu (M θ₂) lamD lamS T < lamS * T * scaleCDF (M θ₂).seller p :=
                hltdiv _ _ _ hLS hq2
              have hμ12 : lamS * T * scaleCDF (M θ₂).seller p ≤ lamS * T * scaleCDF (M θ₁).seller p :=
                mul_le_mul_of_nonneg_left hFle hLS.le
              have hF1p := hF1.1
              have hF2p := hF2.1
              have hm1 := lt_of_lt_of_le hμ1 (hmum (M θ₁))
              have hV2 := hAbove _ _ hμ2 (lt_of_le_of_lt hμ12 hm1)
              have hV1 := hBelow _ hR1 _ (mul_pos hLS hF1.1) hμ1
              rw [hVS _ _ hF1.1 hF1.2] at hV1
              rw [hVS _ _ hF2.1 hF2.2, hbuy] at hV2
              have hm1d := lt_of_lt_of_le hm1 (min_le_left _ _)
              have t1 : 0 < lamS * T * scaleCDF (M θ₂).seller p / (lamD * T) := by positivity
              have t2 := hdivmono _ _ _ hLT hμ12
              have t3 : lamS * T * scaleCDF (M θ₁).seller p / (lamD * T) < 1 := by rwa [div_lt_one hLT]
              have hψ := hR1.1 (hQint (M θ₁).buyer (1 - lamS * T * scaleCDF (M θ₁).seller p / (lamD * T))
                  (by linarith) (by linarith))
                (hQint (M θ₁).buyer (1 - lamS * T * scaleCDF (M θ₂).seller p / (lamD * T))
                  (by linarith) (by linarith))
                (hQmono _ _ _ (by linarith) (by linarith) (by linarith))
              have hf1 := (M θ₁).seller.positive p hl1 hh1
              have hf2 := (M θ₂).seller.positive p hi2.1 hi2.2
              have hig := hI1 (show p / r ∈ {c : ℝ | (M θ₁).seller.lo ≤ (c : EReal) ∧ (c : EReal) ≤ (M θ₁).seller.hi ∧
                  0 < scaleCDF (M θ₁).seller c} from ⟨hl1'.le, hh1'.le, hF1'.1⟩)
                (show p ∈ {c : ℝ | (M θ₁).seller.lo ≤ (c : EReal) ∧ (c : EReal) ≤ (M θ₁).seller.hi ∧
                  0 < scaleCDF (M θ₁).seller c} from ⟨hl1.le, hh1.le, hF1.1⟩) hprle
              have hgood' : r * (M θ₂).seller.pdf p = (M θ₁).seller.pdf (p / r) := hgood
              simp only [] at hig
              rw [← hcdf', ← hgood'] at hig
              have hig2 : p * ((M θ₁).seller.pdf p / scaleCDF (M θ₁).seller p) ≤
                  p * ((M θ₂).seller.pdf p / scaleCDF (M θ₂).seller p) := by
                refine le_trans (le_of_eq ?_) (le_trans hig (le_of_eq ?_))
                · ring
                · field_simp
              have hig3 := le_of_mul_le_mul_left hig2 hp0
              have hig4 : scaleCDF (M θ₂).seller p / (M θ₂).seller.pdf p ≤
                  scaleCDF (M θ₁).seller p / (M θ₁).seller.pdf p := by
                rw [div_le_div_iff₀ hF1p hF2p] at hig3
                rw [div_le_div_iff₀ hf2 hf1]
                linarith
              have hφ : scaleVirtualS (M θ₂).seller p ≤ scaleVirtualS (M θ₁).seller p := by
                unfold scaleVirtualS; linarith
              linarith
          · clear hBuyerValue hSellerValue hdivmono hmono hnn hsupp hIoc hstrict0 hstrictL hstrictR hcont hQF hFQ hQint hQlt hltQ hQmono hSQlt hltSQ hSQlo hSQhi hSQ hBS hBQ hdens hLT hLS hVanti hm0 hbdd hmu0 hmum hAbove hBelow hVB hVS hdivlt hltdiv
            open MeasureTheory ProbabilityTheory in
            (
              have hbuild : ∀ (lo hi : ℝ) (f : ℝ → ℝ), lo < hi → Measurable f → (∀ x ∈ Set.Icc lo hi, 0 < f x) →
                  IntervalIntegrable f volume lo hi → ∫ x in lo..hi, f x = 1 →
                  ∃ D : ScaleDistribution, D.lo = (lo : EReal) ∧ D.hi = (hi : EReal) ∧
                    (∀ x, scaleCDF D x = ∫ z in lo..(max lo (min x hi)), f z) ∧
                    ∀ x ∈ Set.Icc lo hi, D.pdf x = f x := by
                intro lo hi f hlh hfm hpos hii h1
                set g : ℝ → ℝ := (Set.Icc lo hi).indicator f with hg
                have hgnn : ∀ x, 0 ≤ g x := by
                  intro x; simp only [hg, Set.indicator]; split_ifs with h
                  · exact (hpos x h).le
                  · exact le_rfl
                have hgm : Measurable g := hfm.indicator measurableSet_Icc
                have hfI : IntegrableOn f (Set.Icc lo hi) := (intervalIntegrable_iff_integrableOn_Icc_of_le hlh.le).1 hii
                have hgI : Integrable g := hfI.integrable_indicator measurableSet_Icc
                set law : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (g x)) with hlaw
                have hset : ∀ s : Set ℝ, MeasurableSet s → law s = ENNReal.ofReal (∫ x in s ∩ Set.Icc lo hi, f x) := by
                  intro s hs
                  rw [hlaw, withDensity_apply _ hs, ← ofReal_integral_eq_lintegral_ofReal hgI.integrableOn
                    (Filter.Eventually.of_forall hgnn), hg, setIntegral_indicator measurableSet_Icc]
                have hG : ∀ x : ℝ, ∫ z in Set.Iic x ∩ Set.Icc lo hi, f z = ∫ z in lo..(max lo (min x hi)), f z := by
                  intro x
                  by_cases hx : x < lo
                  · have : Set.Iic x ∩ Set.Icc lo hi = ∅ := by
                      ext z; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, Set.mem_empty_iff_false, iff_false]
                      intro ⟨a, b, _⟩; linarith
                    rw [this, Measure.restrict_empty, integral_zero_measure]
                    have : max lo (min x hi) = lo := by
                      apply max_eq_left; exact (min_le_left _ _).trans hx.le
                    rw [this, intervalIntegral.integral_same]
                  · push_neg at hx
                    have hc : max lo (min x hi) = min x hi := max_eq_right (le_min hx hlh.le)
                    have : Set.Iic x ∩ Set.Icc lo hi = Set.Icc lo (min x hi) := by
                      ext z; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, le_min_iff]; tauto
                    rw [this, hc, intervalIntegral.integral_of_le (le_min hx hlh.le), integral_Icc_eq_integral_Ioc]
                have hprob : IsProbabilityMeasure law := by
                  constructor
                  rw [hset _ MeasurableSet.univ, Set.univ_inter, integral_Icc_eq_integral_Ioc,
                    ← intervalIntegral.integral_of_le hlh.le, h1, ENNReal.ofReal_one]
                have hcdf : ∀ x, cdf law x = ∫ z in lo..(max lo (min x hi)), f z := by
                  intro x
                  rw [cdf_eq_real, measureReal_def, hset _ measurableSet_Iic, hG, ENNReal.toReal_ofReal]
                  apply intervalIntegral.integral_nonneg (le_max_left _ _)
                  intro z hz
                  exact (hpos z ⟨hz.1, hz.2.trans (max_le hlh.le (min_le_right _ _))⟩).le
                have hsub : ∀ a b : ℝ, lo ≤ a → a ≤ b → b ≤ hi → IntervalIntegrable f volume a b := by
                  intro a b ha hab hb
                  apply hii.mono_set
                  rw [Set.uIcc_of_le hlh.le, Set.uIcc_of_le hab]
                  exact Set.Icc_subset_Icc ha hb
                have hsupp : ∀ x : ℝ, (0 < cdf law x ∧ cdf law x < 1) ↔ ((lo : EReal) < (x : EReal) ∧ (x : EReal) < (hi : EReal)) := by
                  intro x
                  rw [EReal.coe_lt_coe_iff, EReal.coe_lt_coe_iff, hcdf]
                  set c := max lo (min x hi) with hc
                  have hclo : lo ≤ c := le_max_left _ _
                  have hchi : c ≤ hi := max_le hlh.le (min_le_right _ _)
                  have hadd : (∫ z in lo..c, f z) + (∫ z in c..hi, f z) = 1 := by
                    rw [intervalIntegral.integral_add_adjacent_intervals (hsub _ _ le_rfl hclo hchi) (hsub _ _ hclo hchi le_rfl), h1]
                  constructor
                  · rintro ⟨ha, hb⟩
                    have hc1 : lo < c := by
                      rcases eq_or_lt_of_le hclo with h | h
                      · rw [← h, intervalIntegral.integral_same] at ha; exact absurd ha (lt_irrefl _)
                      · exact h
                    have hc2 : c < hi := by
                      rcases eq_or_lt_of_le hchi with h | h
                      · rw [h] at hb; linarith
                      · exact h
                    constructor
                    · by_contra hh; push_neg at hh
                      have : c = lo := by rw [hc]; exact max_eq_left ((min_le_left _ _).trans hh)
                      linarith
                    · by_contra hh; push_neg at hh
                      have : c = hi := by rw [hc, min_eq_right hh]; exact max_eq_right hlh.le
                      linarith
                  · rintro ⟨ha, hb⟩
                    have hcx : c = x := by rw [hc, min_eq_left hb.le]; exact max_eq_right ha.le
                    rw [hcx] at hadd ⊢
                    have p1 : 0 < ∫ z in lo..x, f z :=
                      intervalIntegral.intervalIntegral_pos_of_pos_on (hsub _ _ le_rfl ha.le hb.le)
                        (fun z hz => hpos z ⟨hz.1.le, (hz.2.trans hb).le⟩) ha
                    have p2 : 0 < ∫ z in x..hi, f z :=
                      intervalIntegral.intervalIntegral_pos_of_pos_on (hsub _ _ ha.le hb.le le_rfl)
                        (fun z hz => hpos z ⟨(ha.trans hz.1).le, hz.2.le⟩) hb
                    constructor <;> linarith
                refine ⟨⟨lo, hi, law, g, EReal.coe_lt_coe_iff.2 hlh, hprob, hgm, hgnn, rfl, hsupp, ?_⟩,
                  rfl, rfl, hcdf, ?_⟩
                · intro x h1 h2
                  rw [EReal.coe_lt_coe_iff] at h1 h2
                  show 0 < g x
                  simp only [hg, Set.indicator_of_mem (show x ∈ Set.Icc lo hi from ⟨h1.le, h2.le⟩)]
                  exact hpos x ⟨h1.le, h2.le⟩
                · intro x hx
                  show g x = f x
                  simp only [hg, Set.indicator_of_mem hx]
              have hsInf : ∀ (S : Set ℝ) (lo hi : ℝ), hi ∈ S → (∀ x ∈ S, lo ≤ x) →
                  (∀ x y, x ∈ S → x ≤ y → y ∈ S) → sInf S = sInf {x | x ∈ Set.Icc lo hi ∧ x ∈ S} := by
                intro S lo hi hh hlo hup
                have hb : BddBelow S := ⟨lo, hlo⟩
                have hne : ({x | x ∈ Set.Icc lo hi ∧ x ∈ S}).Nonempty := ⟨hi, ⟨hlo hi hh, le_rfl⟩, hh⟩
                have hbb : BddBelow {x | x ∈ Set.Icc lo hi ∧ x ∈ S} := ⟨lo, fun y hy => hy.1.1⟩
                have hmem : hi ∈ {x | x ∈ Set.Icc lo hi ∧ x ∈ S} := ⟨⟨hlo hi hh, le_rfl⟩, hh⟩
                apply le_antisymm
                · exact csInf_le_csInf hb hne (fun x hx => hx.2)
                · apply le_csInf ⟨hi, hh⟩
                  intro x hx
                  by_cases hxh : x ≤ hi
                  · exact csInf_le hbb ⟨⟨hlo x hx, hxh⟩, hx⟩
                  · push_neg at hxh
                    exact (csInf_le hbb hmem).trans hxh.le
              intro E hE hloS
              obtain ⟨DB, hBlo, hBhi, hBcdf, hBpdf⟩ := hbuild E.loB E.hiB E.fB E.loB_lt_hiB E.fB_measurable
                E.fB_pos E.fB_intervalIntegrable E.fB_integral
              obtain ⟨DS, hSlo, hShi, hScdf, hSpdf⟩ := hbuild E.loS E.hiS E.fS E.loS_lt_hiS E.fS_measurable
                E.fS_pos E.fS_intervalIntegrable E.fS_integral
              have hFd : ∀ x, scaleCDF DB x = Fd E x := fun x => hBcdf x
              have hFs : ∀ x, scaleCDF DS x = Fs E x := fun x => hScdf x
              refine ⟨⟨DB, DS⟩, ⟨hBlo, hBhi, hSlo, hShi, hFd, hFs, hBpdf, hSpdf⟩, ?_⟩
              have hFdIcc : ∀ x ∈ Set.Icc E.loB E.hiB, Fd E x = E.cdfB x := by
                intro x hx; unfold Fd; rw [min_eq_left hx.2, max_eq_right hx.1]
              have hFsIcc : ∀ x ∈ Set.Icc E.loS E.hiS, Fs E x = E.cdfS x := by
                intro x hx; unfold Fs; rw [min_eq_left hx.2, max_eq_right hx.1]
              have hFd0 : ∀ x, x ≤ E.loB → Fd E x = 0 := by
                intro x hx; unfold Fd
                rw [max_eq_left ((min_le_left _ _).trans hx)]
                unfold MechanismDesign.BilateralTrade.Environment.cdfB; exact intervalIntegral.integral_same
              have hFs0 : ∀ x, x ≤ E.loS → Fs E x = 0 := by
                intro x hx; unfold Fs
                rw [max_eq_left ((min_le_left _ _).trans hx)]
                unfold MechanismDesign.BilateralTrade.Environment.cdfS; exact intervalIntegral.integral_same
              have hFd1 : ∀ x, E.hiB ≤ x → Fd E x = 1 := by
                intro x hx; unfold Fd
                rw [min_eq_right hx, max_eq_right E.loB_lt_hiB.le]
                exact E.fB_integral
              have hFs1 : ∀ x, E.hiS ≤ x → Fs E x = 1 := by
                intro x hx; unfold Fs
                rw [min_eq_right hx, max_eq_right E.loS_lt_hiS.le]
                exact E.fS_integral
              have hFdlt : ∀ x, x < E.hiB → Fd E x < 1 := by
                intro x hx
                by_cases h : x ≤ E.loB
                · rw [hFd0 x h]; norm_num
                · push_neg at h
                  have := ((DB.support x).2 ⟨by rw [hBlo]; exact EReal.coe_lt_coe_iff.2 h,
                    by rw [hBhi]; exact EReal.coe_lt_coe_iff.2 hx⟩).2
                  rw [← hFd]; exact this
              have hFspos : ∀ x, E.loS < x → 0 < Fs E x := by
                intro x hx
                by_cases h : E.hiS ≤ x
                · rw [hFs1 x h]; norm_num
                · push_neg at h
                  have := ((DS.support x).2 ⟨by rw [hSlo]; exact EReal.coe_lt_coe_iff.2 hx,
                    by rw [hShi]; exact EReal.coe_lt_coe_iff.2 h⟩).1
                  rw [← hFs]; exact this
              have hFdmono : Monotone (Fd E) := by
                intro a b hab; rw [← hFd, ← hFd]; haveI := DB.probability; exact (cdf DB.law).mono hab
              have hFsmono : Monotone (Fs E) := by
                intro a b hab; rw [← hFs, ← hFs]; haveI := DS.probability; exact (cdf DS.law).mono hab
              have hFdnn : ∀ x, 0 ≤ Fd E x := by
                intro x; rw [← hFd]; haveI := DB.probability; exact cdf_nonneg _ _
              have hFsnn : ∀ x, 0 ≤ Fs E x := by
                intro x; rw [← hFs]; haveI := DS.probability; exact cdf_nonneg _ _
              -- inverse functions
              have hBIbdd : ∀ q, BddBelow {p : ℝ | p ∈ Set.Icc E.loB E.hiB ∧ FdBar E p ≤ q} :=
                fun q => ⟨E.loB, fun y hy => hy.1.1⟩
              have hSIbdd : ∀ q, BddBelow {w : ℝ | w ∈ Set.Icc E.loS E.hiS ∧ q ≤ Fs E w} :=
                fun q => ⟨E.loS, fun y hy => hy.1.1⟩
              have hBIhi : ∀ q, 0 ≤ q → E.hiB ∈ {p : ℝ | p ∈ Set.Icc E.loB E.hiB ∧ FdBar E p ≤ q} := by
                intro q hq; refine ⟨⟨E.loB_lt_hiB.le, le_rfl⟩, ?_⟩; unfold FdBar; rw [hFd1 _ le_rfl]; linarith
              have hSIhi : ∀ q, q ≤ 1 → E.hiS ∈ {w : ℝ | w ∈ Set.Icc E.loS E.hiS ∧ q ≤ Fs E w} := by
                intro q hq; refine ⟨⟨E.loS_lt_hiS.le, le_rfl⟩, ?_⟩; rw [hFs1 _ le_rfl]; exact hq
              have hBImem : ∀ q, 0 ≤ q → FdBarInv E q ∈ Set.Icc E.loB E.hiB := by
                intro q hq
                exact ⟨le_csInf ⟨_, hBIhi q hq⟩ (fun y hy => hy.1.1), csInf_le (hBIbdd q) (hBIhi q hq)⟩
              have hSImem : ∀ q, q ≤ 1 → FsInv E q ∈ Set.Icc E.loS E.hiS := by
                intro q hq
                exact ⟨le_csInf ⟨_, hSIhi q hq⟩ (fun y hy => hy.1.1), csInf_le (hSIbdd q) (hSIhi q hq)⟩
              have hBIanti : ∀ q₁ q₂, 0 ≤ q₁ → q₁ ≤ q₂ → FdBarInv E q₂ ≤ FdBarInv E q₁ := by
                intro q₁ q₂ h0 h12
                exact csInf_le_csInf (hBIbdd q₂) ⟨_, hBIhi q₁ h0⟩ (fun y hy => ⟨hy.1, hy.2.trans h12⟩)
              have hSImono : ∀ q₁ q₂, q₁ ≤ q₂ → q₂ ≤ 1 → FsInv E q₁ ≤ FsInv E q₂ := by
                intro q₁ q₂ h12 h1
                exact csInf_le_csInf (hSIbdd q₁) ⟨_, hSIhi q₂ h1⟩ (fun y hy => ⟨hy.1, h12.trans hy.2⟩)
              have hBI0 : FdBarInv E 0 = E.hiB := by
                apply le_antisymm (csInf_le (hBIbdd 0) (hBIhi 0 le_rfl))
                apply le_csInf ⟨_, hBIhi 0 le_rfl⟩
                intro y hy
                by_contra hc; push_neg at hc
                have := hFdlt y hc; have := hy.2; unfold FdBar at this; linarith
              have hBI1 : FdBarInv E 1 = E.loB := by
                apply le_antisymm _ (hBImem 1 zero_le_one).1
                apply csInf_le (hBIbdd 1)
                refine ⟨⟨le_rfl, E.loB_lt_hiB.le⟩, ?_⟩
                unfold FdBar; linarith [hFdnn E.loB]
              have hSI0 : FsInv E 0 = E.loS := by
                apply le_antisymm _ (hSImem 0 zero_le_one).1
                exact csInf_le (hSIbdd 0) ⟨⟨le_rfl, E.loS_lt_hiS.le⟩, hFsnn _⟩
              have hSI1 : FsInv E 1 = E.hiS := by
                apply le_antisymm (csInf_le (hSIbdd 1) (hSIhi 1 le_rfl))
                apply le_csInf ⟨_, hSIhi 1 le_rfl⟩
                intro y hy
                by_contra hc; push_neg at hc
                have h1 := hy.2
                have : Fs E y < 1 := by
                  by_cases h : y ≤ E.loS
                  · rw [hFs0 y h]; norm_num
                  · push_neg at h
                    have := ((DS.support y).2 ⟨by rw [hSlo]; exact EReal.coe_lt_coe_iff.2 h,
                      by rw [hShi]; exact EReal.coe_lt_coe_iff.2 hc⟩).2
                    rw [← hFs]; exact this
                linarith
              have hQB : ∀ q, 0 < q → q < 1 → scaleQuantile DB (1 - q) = FdBarInv E q := by
                intro q h0 h1
                unfold scaleQuantile FdBarInv
                rw [hsInf {x | 1 - q ≤ scaleCDF DB x} E.loB E.hiB ?_ ?_ ?_]
                · congr 1; ext p
                  simp only [Set.mem_setOf_eq, hFd, FdBar]
                  constructor <;> rintro ⟨a, b⟩ <;> exact ⟨a, by linarith⟩
                · show 1 - q ≤ scaleCDF DB E.hiB
                  rw [hFd, hFd1 _ le_rfl]; linarith
                · intro x hx
                  by_contra hc; push_neg at hc
                  have : 1 - q ≤ scaleCDF DB x := hx
                  rw [hFd, hFd0 x hc.le] at this; linarith
                · intro x y hx hxy
                  show 1 - q ≤ scaleCDF DB y
                  have : 1 - q ≤ scaleCDF DB x := hx
                  rw [hFd] at this ⊢; exact this.trans (hFdmono hxy)
              have hQS : ∀ q, 0 < q → q < 1 → scaleQuantile DS q = FsInv E q := by
                intro q h0 h1
                unfold scaleQuantile FsInv
                rw [hsInf {x | q ≤ scaleCDF DS x} E.loS E.hiS ?_ ?_ ?_]
                · congr 1; ext p
                  simp only [Set.mem_setOf_eq, hFs]
                · show q ≤ scaleCDF DS E.hiS
                  rw [hFs, hFs1 _ le_rfl]; linarith
                · intro x hx
                  by_contra hc; push_neg at hc
                  have : q ≤ scaleCDF DS x := hx
                  rw [hFs, hFs0 x hc.le] at this; linarith
                · intro x y hx hxy
                  show q ≤ scaleCDF DS y
                  have : q ≤ scaleCDF DS x := hx
                  rw [hFs] at this ⊢; exact this.trans (hFsmono hxy)
              set m := min (lamD * T) (lamS * T) with hm
              have hm0 : 0 < m := lt_min (by positivity) (by positivity)
              have hmD : m ≤ lamD * T := min_le_left _ _
              have hmS : m ≤ lamS * T := min_le_right _ _
              have hVanti : ∀ μ₁ μ₂, 0 ≤ μ₁ → μ₁ ≤ μ₂ → μ₂ ≤ m → V E lamD lamS T μ₂ ≤ V E lamD lamS T μ₁ := by
                intro μ₁ μ₂ h0 h12 h2
                unfold V
                have q0 : 0 ≤ μ₁ / (lamD * T) := by positivity
                have q12 : μ₁ / (lamD * T) ≤ μ₂ / (lamD * T) := div_le_div_of_nonneg_right h12 (by positivity)
                have s12 : μ₁ / (lamS * T) ≤ μ₂ / (lamS * T) := div_le_div_of_nonneg_right h12 (by positivity)
                have s2 : μ₂ / (lamS * T) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
                have a := hE.2 (hBImem _ (q0.trans q12)) (hBImem _ q0) (hBIanti _ _ q0 q12)
                have b := hE.1 (hSImem _ (s12.trans s2)) (hSImem _ s2) (hSImono _ _ s12 s2)
                linarith
              have hVeq : ∀ μ, 0 < μ → μ < m → scaleV ⟨DB, DS⟩ lamD lamS T μ = V E lamD lamS T μ := by
                intro μ h0 h1
                have q0 : 0 < μ / (lamD * T) := by positivity
                have q1 : μ / (lamD * T) < 1 := by rw [div_lt_one (by positivity)]; linarith
                have s0 : 0 < μ / (lamS * T) := by positivity
                have s1 : μ / (lamS * T) < 1 := by rw [div_lt_one (by positivity)]; linarith
                unfold scaleV V
                simp only
                rw [hQB _ q0 q1, hQS _ s0 s1]
                have mb := hBImem _ q0.le
                have ms := hSImem _ s1.le
                unfold scaleVirtualB scaleVirtualS scaleSurvival
                rw [hFd, hFs, hFdIcc _ mb, hFsIcc _ ms, hBpdf _ mb, hSpdf _ ms]
                rfl
              have hmuEq : scaleMu ⟨DB, DS⟩ lamD lamS T = muStar E lamD lamS T := by
                unfold scaleMu muStar
                rw [← hm]
                set B := ({0} ∪ {μ | μ ∈ Set.Ioo 0 m ∧ 0 ≤ scaleV ⟨DB, DS⟩ lamD lamS T μ}) with hB
                set A := {μ : ℝ | μ ∈ Set.Icc 0 m ∧ 0 ≤ V E lamD lamS T μ} with hA
                have hBbdd : BddAbove B := by
                  refine ⟨m, ?_⟩
                  rintro x (hx | hx)
                  · rw [Set.mem_singleton_iff.1 hx]; exact hm0.le
                  · exact hx.1.2.le
                have hBne : B.Nonempty := ⟨0, Or.inl rfl⟩
                have hB0 : 0 ≤ sSup B := le_csSup hBbdd (Or.inl rfl)
                by_cases hAe : A = ∅
                · rw [hAe, Real.sSup_empty]
                  apply le_antisymm _ hB0
                  apply csSup_le hBne
                  rintro x (hx | hx)
                  · rw [Set.mem_singleton_iff.1 hx]
                  · exfalso
                    have hV0 : V E lamD lamS T 0 < 0 := by
                      by_contra hc; push_neg at hc
                      have : (0:ℝ) ∈ A := ⟨⟨le_rfl, hm0.le⟩, hc⟩
                      rw [hAe] at this; exact this
                    have := hx.2
                    rw [hVeq x hx.1.1 hx.1.2] at this
                    linarith [hVanti 0 x le_rfl hx.1.1.le hx.1.2.le]
                · have hAbdd : BddAbove A := ⟨m, fun x hx => hx.1.2⟩
                  have hAne : A.Nonempty := Set.nonempty_iff_ne_empty.2 hAe
                  apply le_antisymm
                  · apply csSup_le hBne
                    rintro x (hx | hx)
                    · rw [Set.mem_singleton_iff.1 hx]
                      obtain ⟨a, ha⟩ := hAne
                      exact (ha.1.1).trans (le_csSup hAbdd ha)
                    · apply le_csSup hAbdd
                      refine ⟨⟨hx.1.1.le, hx.1.2.le⟩, ?_⟩
                      rw [← hVeq x hx.1.1 hx.1.2]; exact hx.2
                  · apply csSup_le hAne
                    intro μ hμ
                    by_contra hc; push_neg at hc
                    set ν := (sSup B + μ) / 2 with hν
                    have hν0 : 0 < ν := by rw [hν]; linarith
                    have hνμ : ν < μ := by rw [hν]; linarith
                    have hνB : ν ∈ B := by
                      right
                      refine ⟨⟨hν0, by linarith [hμ.1.2]⟩, ?_⟩
                      rw [hVeq ν hν0 (by linarith [hμ.1.2])]
                      linarith [hVanti ν μ hν0.le hνμ.le hμ.1.2, hμ.2]
                    have := le_csSup hBbdd hνB
                    rw [hν] at this; linarith
              have hBbdd' : BddAbove ({0} ∪ {μ | μ ∈ Set.Ioo 0 m ∧ 0 ≤ scaleV ⟨DB, DS⟩ lamD lamS T μ}) := by
                refine ⟨m, ?_⟩
                rintro x (hx | hx)
                · rw [Set.mem_singleton_iff.1 hx]; exact hm0.le
                · exact hx.1.2.le
              have hmu0 : 0 ≤ scaleMu ⟨DB, DS⟩ lamD lamS T := by
                unfold scaleMu
                rw [← hm]
                exact le_csSup hBbdd' (Set.mem_union_left _ rfl)
              have hmum : scaleMu ⟨DB, DS⟩ lamD lamS T ≤ m := by
                unfold scaleMu
                rw [← hm]
                apply csSup_le (Set.nonempty_of_mem (Set.mem_union_left _ (Set.mem_singleton (0:ℝ))))
                rintro x (hx | hx)
                · rw [Set.mem_singleton_iff.1 hx]; exact hm0.le
                · exact hx.1.2.le
              refine ⟨hmuEq, ?_, ?_, ?_⟩
              · unfold scaleP pStar
                rw [← hmuEq]
                set q := scaleMu ⟨DB, DS⟩ lamD lamS T / (lamD * T) with hq
                have q0 : 0 ≤ q := by positivity
                have q1 : q ≤ 1 := by rw [hq, div_le_one (by positivity)]; linarith
                unfold scaleBuyerQuantile
                simp only
                split_ifs with h1 h2
                · rw [le_antisymm h1 q0, hBI0, hBhi]
                · rw [le_antisymm q1 h2, hBI1, hBlo]
                · push_neg at h1 h2; rw [hQB q h1 h2]
              · unfold scaleW wStar
                rw [← hmuEq]
                set q := scaleMu ⟨DB, DS⟩ lamD lamS T / (lamS * T) with hq
                have q0 : 0 ≤ q := by positivity
                have q1 : q ≤ 1 := by rw [hq, div_le_one (by positivity)]; linarith
                unfold scaleSellerQuantile
                simp only
                split_ifs with h1 h2
                · rw [le_antisymm h1 q0, hSI0, hSlo]
                · rw [le_antisymm q1 h2, hSI1, hShi]
                · push_neg at h1 h2; rw [hQS q h1 h2]
              have hSurv : scaleSurvival DB = FdBar E := funext fun x => by unfold scaleSurvival FdBar; rw [hFd]
              have hCdfS : scaleCDF DS = Fs E := funext hFs
              have hset : {z : EReal | ∃ π, ScaleFeasible ⟨DB, DS⟩ lamD lamS T π ∧
                  z = (scaleObjective ⟨DB, DS⟩ lamD lamS T π : EReal)} =
                  (fun v : ℝ => (v : EReal)) '' {v : ℝ | ∃ π : ℝ → ℝ × ℝ,
                    IsFeasiblePath E lamD lamS T π ∧ v = fluidObjective E lamD lamS T π} := by
                ext z
                simp only [ScaleFeasible, scaleObjective, IsFeasiblePath, fluidObjective, hSurv, hCdfS,
                  Set.mem_setOf_eq, Set.mem_image]
                constructor
                · rintro ⟨π, hπ, rfl⟩; exact ⟨_, ⟨π, hπ, rfl⟩, rfl⟩
                · rintro ⟨_, ⟨π, hπ, rfl⟩, rfl⟩; exact ⟨π, hπ, rfl⟩
              have hbdd : BddAbove {v : ℝ | ∃ π : ℝ → ℝ × ℝ,
                    IsFeasiblePath E lamD lamS T π ∧ v = fluidObjective E lamD lamS T π} := by
                refine ⟨T * (lamD * |E.hiB|), ?_⟩
                rintro v ⟨π, ⟨hmeas, hpt, hi1, hi2⟩, rfl⟩
                unfold fluidObjective
                have h1 : (∫ t in (0:ℝ)..T, lamD * (π t).1 * FdBar E (π t).1) ≤
                    ∫ t in (0:ℝ)..T, lamD * |E.hiB| := by
                  apply intervalIntegral.integral_mono_on hT.le hi1 intervalIntegrable_const
                  intro t ht
                  obtain ⟨a, b, c⟩ := hpt t ht
                  set p := (π t).1
                  by_cases hp : E.hiB ≤ p
                  · have : FdBar E p = 0 := by unfold FdBar; rw [hFd1 p hp]; ring
                    rw [this]; simp only [mul_zero]; positivity
                  · push_neg at hp
                    have f0 : 0 ≤ FdBar E p := by unfold FdBar; linarith [hFdlt p hp]
                    have f1 : FdBar E p ≤ 1 := by unfold FdBar; linarith [hFdnn p]
                    have : p ≤ |E.hiB| := hp.le.trans (le_abs_self _)
                    have : p * FdBar E p ≤ |E.hiB| :=
                      (mul_le_of_le_one_right a f1).trans this
                    rw [mul_assoc]
                    exact mul_le_mul_of_nonneg_left this hD.le
                have h2 : 0 ≤ ∫ t in (0:ℝ)..T, lamS * (π t).2 * Fs E (π t).2 := by
                  apply intervalIntegral.integral_nonneg hT.le
                  intro t ht
                  have := (hpt t ht).2.1
                  have := hFsnn (π t).2
                  positivity
                rw [intervalIntegral.integral_const, smul_eq_mul] at h1
                linarith
              have hne : ({v : ℝ | ∃ π : ℝ → ℝ × ℝ,
                    IsFeasiblePath E lamD lamS T π ∧ v = fluidObjective E lamD lamS T π}).Nonempty := by
                refine ⟨_, fun _ => (max E.hiB 0, 0), ⟨measurable_const, ?_, ?_, ?_⟩, rfl⟩
                · intro t ht
                  refine ⟨le_max_right _ _, le_rfl, ?_⟩
                  have e1 : FdBar E (max E.hiB 0) = 0 := by unfold FdBar; rw [hFd1 _ (le_max_left _ _)]; ring
                  have e2 : Fs E 0 = 0 := hFs0 0 hloS
                  simp only [e1, e2, mul_zero]
                · exact intervalIntegrable_const
                · exact intervalIntegrable_const
              unfold scaleValue fluidValue
              rw [hset]
              exact (Monotone.map_csSup_of_continuousAt continuous_coe_real_ereal.continuousAt
                (fun a b h => EReal.coe_le_coe_iff.2 h) hne hbdd).symm)
