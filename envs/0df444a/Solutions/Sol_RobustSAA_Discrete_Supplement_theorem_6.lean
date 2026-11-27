-- Prove2me | solution 1 for RobustSAA.Discrete.Supplement.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:13:10.918629+00:00
-- url     : https://prove2.me/submissions/8e145fb0-758b-4215-a66e-adbd835317c8

import Mathlib
import Definitions.Def_RobustSAA_Convergence_Setting
import Definitions.Def_RobustSAA_Discrete_Supplement_LCX

open RobustSAA
open RobustSAA.Discrete
open RobustSAA.Discrete.Supplement

open MeasureTheory Filter Topology RobustSAA.Convergence

theorem solution {d : ℕ} (Ξ : Set (Pt d)) (hΞ : IsClosed Ξ) (QC QR : ℕ → ℝ)
    (hQC : Tendsto QC atTop (𝓝 0)) (hQR : Tendsto QR atTop (𝓝 0)) :
    IsConsistentOn (fun F₀ : ProbabilityMeasure ↥Ξ => secondMoment F₀ < ⊤)
      (lcxDUS QC QR) := by
        classical
        have L1 : ∀ (F : ProbabilityMeasure ↥Ξ) (g : ↥Ξ → ℝ), Continuous g → Integrable g (F : Measure ↥Ξ) →
            ∀ (t : ℕ → ℝ) (t0 : ℝ), Tendsto t atTop (𝓝 t0) → t0 < ∫ ξ, g ξ ∂(F : Measure ↥Ξ) →
            ∀ A : ℕ → Set (ℕ → ↥Ξ), (∀ N, A N ⊆ {ω | (∑ i ∈ Finset.range N, g (ω i)) / N ≤ t N}) →
            Tendsto (fun N => dataLaw F (A N)) atTop (𝓝 0) := by
          intro F g hf hiF t t0 ht ht0 A hA
          have hmp : ∀ i : ℕ, MeasurePreserving (Function.eval i) (dataLaw F) (F : Measure ↥Ξ) :=
            fun i => measurePreserving_eval_infinitePi (fun _ : ℕ => (F : Measure ↥Ξ)) i
          have hSL : ∀ᵐ ω ∂(dataLaw F),
              Tendsto (fun N : ℕ => (∑ i ∈ Finset.range N, g (ω i)) / N) atTop
                (𝓝 (∫ ξ, g ξ ∂(F : Measure ↥Ξ))) := by
            have h := ProbabilityTheory.strong_law_ae_real (μ := dataLaw F) (fun (i : ℕ) (ω : ℕ → ↥Ξ) => g (ω i))
              ((hmp 0).integrable_comp_of_integrable hiF) ?_ ?_
            · have e : ∫ ω, g (ω 0) ∂(dataLaw F) = ∫ ξ, g ξ ∂(F : Measure ↥Ξ) := by
                rw [← (hmp 0).map_eq, integral_map (hmp 0).measurable.aemeasurable
                  hf.measurable.aestronglyMeasurable]
              rw [e] at h
              exact h
            · have hI := ProbabilityTheory.iIndepFun_infinitePi (P := fun _ : ℕ => (F : Measure ↥Ξ))
                (X := fun _ : ℕ => g) (fun _ => hf.measurable)
              intro i j hij
              exact hI.indepFun hij
            · intro i
              refine ⟨(hf.measurable.comp (hmp i).measurable).aemeasurable,
                (hf.measurable.comp (hmp 0).measurable).aemeasurable, ?_⟩
              have e : ∀ i : ℕ, Measure.map (fun ω : ℕ → ↥Ξ => g (ω i)) (dataLaw F) =
                  Measure.map g (F : Measure ↥Ξ) := by
                intro i
                rw [← (hmp i).map_eq, Measure.map_map hf.measurable (hmp i).measurable]
                rfl
              rw [e i, e 0]
          have : IsProbabilityMeasure (dataLaw F) := by unfold dataLaw; infer_instance
          have hmeas : ∀ N : ℕ, AEStronglyMeasurable
              (fun ω : ℕ → ↥Ξ => (∑ i ∈ Finset.range N, g (ω i)) / N) (dataLaw F) := by
            intro N
            refine Measurable.aestronglyMeasurable ?_
            refine Measurable.div_const ?_ _
            refine Finset.measurable_sum _ fun i _ => ?_
            exact hf.measurable.comp (measurable_pi_apply i)
          have hTM := tendstoInMeasure_of_tendsto_ae (g := fun _ => ∫ ξ, g ξ ∂(F : Measure ↥Ξ)) hmeas hSL
          set c := ∫ ξ, g ξ ∂(F : Measure ↥Ξ) with hc
          set δ := (c - t0) / 2 with hδ
          have hδpos : 0 < δ := by rw [hδ]; linarith
          have hT := hTM (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδpos)
          have hev : ∀ᶠ N in atTop, t N < t0 + δ := ht.eventually (gt_mem_nhds (by linarith))
          refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hT
            (Eventually.of_forall fun _ => zero_le) ?_
          filter_upwards [hev] with N hN
          refine measure_mono ?_
          intro ω hω
          have h1 := hA N hω
          simp only [Set.mem_ofPred_eq] at h1 ⊢
          rw [edist_dist, Real.dist_eq]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [abs_sub_comm]
          refine le_trans ?_ (le_abs_self _)
          rw [hδ] at hN ⊢
          linarith
        have L2 : ∀ (P Q : Measure ↥Ξ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q],
            (∀ (v : Pt d) (s : ℝ), Integrable (fun ξ : ↥Ξ => hinge v s (ξ : Pt d)) P) →
            (∀ (v : Pt d) (s : ℝ), Integrable (fun ξ : ↥Ξ => hinge v s (ξ : Pt d)) Q) →
            (∀ (v : Pt d) (s : ℝ), ∫ ξ, hinge v s (ξ : Pt d) ∂P = ∫ ξ, hinge v s (ξ : Pt d) ∂Q) →
            P = Q := by
          intro P Q _ _ hPi hQi heq
          have hX : ∀ t : Pt d, Measurable (fun ξ : ↥Ξ => inner ℝ (ξ : Pt d) t) := by
            intro t
            exact (continuous_subtype_val.inner continuous_const).measurable
          -- ramp identity
          have hramp : ∀ (t : Pt d) (c : ℝ) (ξ : ↥Ξ), max (c - inner ℝ (ξ : Pt d) t) 0 = hinge (-t) (-c) (ξ : Pt d) := by
            intro t c ξ
            unfold hinge
            rw [inner_neg_left, real_inner_comm]
            ring_nf
          have hcdf : ∀ (μ : Measure ↥Ξ) [IsProbabilityMeasure μ] (t : Pt d) (a : ℝ),
              Tendsto (fun n : ℕ => ∫ ξ, ((n : ℝ) + 1) * (max (a + 1 / ((n : ℝ) + 1) - inner ℝ (ξ : Pt d) t) 0 -
                  max (a - inner ℝ (ξ : Pt d) t) 0) ∂μ) atTop
                (𝓝 (μ.real {ξ | inner ℝ (ξ : Pt d) t ≤ a})) := by
            intro μ _ t a
            have hms : MeasurableSet {ξ : ↥Ξ | inner ℝ (ξ : Pt d) t ≤ a} := measurableSet_le (hX t) measurable_const
            rw [← integral_indicator_one hms]
            refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ (integrable_const _) ?_ ?_
            · intro n
              exact (Continuous.aestronglyMeasurable (by fun_prop))
            · intro n
              refine Eventually.of_forall fun ξ => ?_
              set x := inner ℝ (ξ : Pt d) t
              have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
              rw [Real.norm_eq_abs, abs_le]
              have h1 : (n + 1 : ℝ) * (1 / ((n : ℝ) + 1)) = 1 := by field_simp
              constructor
              · have : max (a - x) 0 ≤ max (a + 1 / ((n : ℝ) + 1) - x) 0 :=
                  max_le_max (by have := one_div_pos.mpr hn; linarith) le_rfl
                nlinarith
              · have : max (a + 1 / ((n : ℝ) + 1) - x) 0 - max (a - x) 0 ≤ 1 / ((n : ℝ) + 1) := by
                  rcases le_total 0 (a - x) with h | h
                  · rw [max_eq_left h, max_eq_left (by have := one_div_pos.mpr hn; linarith)]; linarith
                  · rw [max_eq_right h]
                    have : max (a + 1 / ((n : ℝ) + 1) - x) 0 ≤ 1 / ((n : ℝ) + 1) :=
                      max_le (by linarith) (by positivity)
                    linarith
                nlinarith
            · refine Eventually.of_forall fun ξ => ?_
              set x := inner ℝ (ξ : Pt d) t
              by_cases hxa : x ≤ a
              · have : Set.indicator {ξ : ↥Ξ | inner ℝ (ξ : Pt d) t ≤ a} (1 : ↥Ξ → ℝ) ξ = 1 := by
                  simp [x, hxa]
                rw [this]
                refine tendsto_const_nhds.congr fun n => ?_
                have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
                rw [max_eq_left (by have := one_div_pos.mpr hn; linarith), max_eq_left (by linarith)]
                field_simp
                ring
              · have : Set.indicator {ξ : ↥Ξ | inner ℝ (ξ : Pt d) t ≤ a} (1 : ↥Ξ → ℝ) ξ = 0 := by
                  simp [x, hxa]
                rw [this]
                push Not at hxa
                have hev : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) ≤ x - a := by
                  have : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
                    tendsto_one_div_add_atTop_nhds_zero_nat
                  exact (this.eventually (ge_mem_nhds (by linarith)))
                refine tendsto_const_nhds.congr' ?_
                filter_upwards [hev] with n hn
                rw [max_eq_right (by linarith), max_eq_right (by linarith)]
                simp
          have hrampint : ∀ (t : Pt d) (a : ℝ) (n : ℕ),
              ∫ ξ, ((n : ℝ) + 1) * (max (a + 1 / ((n : ℝ) + 1) - inner ℝ (ξ : Pt d) t) 0 -
                  max (a - inner ℝ (ξ : Pt d) t) 0) ∂P =
              ∫ ξ, ((n : ℝ) + 1) * (max (a + 1 / ((n : ℝ) + 1) - inner ℝ (ξ : Pt d) t) 0 -
                  max (a - inner ℝ (ξ : Pt d) t) 0) ∂Q := by
            intro t a n
            simp only [hramp]
            rw [integral_const_mul, integral_const_mul, integral_sub (hPi _ _) (hPi _ _),
              integral_sub (hQi _ _) (hQi _ _), heq, heq]
          have hlaw : ∀ t : Pt d, P.map (fun ξ : ↥Ξ => inner ℝ (ξ : Pt d) t) =
              Q.map (fun ξ : ↥Ξ => inner ℝ (ξ : Pt d) t) := by
            intro t
            refine Measure.ext_of_Iic _ _ fun a => ?_
            rw [Measure.map_apply (hX t) measurableSet_Iic, Measure.map_apply (hX t) measurableSet_Iic]
            have h1 := hcdf P t a
            have h2 := hcdf Q t a
            simp only [hrampint] at h1
            have h3 := tendsto_nhds_unique h1 h2
            have e : (fun ξ : ↥Ξ => inner ℝ (ξ : Pt d) t) ⁻¹' Set.Iic a = {ξ : ↥Ξ | inner ℝ (ξ : Pt d) t ≤ a} := rfl
            rw [e]
            exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h3
          have hemb : MeasurableEmbedding (Subtype.val : ↥Ξ → Pt d) :=
            MeasurableEmbedding.subtype_coe hΞ.measurableSet
          have hmap : P.map (Subtype.val : ↥Ξ → Pt d) = Q.map (Subtype.val : ↥Ξ → Pt d) := by
            refine Measure.ext_of_charFun (funext fun t => ?_)
            rw [charFun_apply, charFun_apply, hemb.integral_map, hemb.integral_map]
            have hg : ∀ (μ : Measure ↥Ξ), ∫ ξ, Complex.exp (↑(inner ℝ (ξ : Pt d) t) * Complex.I) ∂μ =
                ∫ x, Complex.exp (↑x * Complex.I) ∂(μ.map (fun ξ : ↥Ξ => inner ℝ (ξ : Pt d) t)) := by
              intro μ
              rw [integral_map (hX t).aemeasurable (by fun_prop)]
            rw [hg P, hg Q, hlaw t]
          rw [← hemb.comap_map P, ← hemb.comap_map Q, hmap]
        have L3a : ∀ (P Q : Measure ↥Ξ),
            (∀ (a : Pt d) (b : ℝ), l1norm a + |b| ≤ 1 →
              ∫⁻ ξ, ENNReal.ofReal (hinge a b (ξ : Pt d)) ∂P ≤ ∫⁻ ξ, ENNReal.ofReal (hinge a b (ξ : Pt d)) ∂Q) →
            ∀ (a : Pt d) (b : ℝ),
              ∫⁻ ξ, ENNReal.ofReal (hinge a b (ξ : Pt d)) ∂P ≤ ∫⁻ ξ, ENNReal.ofReal (hinge a b (ξ : Pt d)) ∂Q := by
          intro P Q h a b
          have hl : 0 ≤ l1norm a := Finset.sum_nonneg fun _ _ => abs_nonneg _
          set c : ℝ := l1norm a + |b| + 1 with hc
          have hcpos : 0 < c := by have := abs_nonneg b; linarith
          have hscale : ∀ ξ : Pt d, hinge (c⁻¹ • a) (c⁻¹ * b) ξ = c⁻¹ * hinge a b ξ := by
            intro ξ
            unfold hinge
            rw [real_inner_smul_left, ← mul_sub, mul_max_of_nonneg _ _ (inv_nonneg.mpr hcpos.le), mul_zero]
          have hle : l1norm (c⁻¹ • a) + |c⁻¹ * b| ≤ 1 := by
            have e1 : l1norm (c⁻¹ • a) = c⁻¹ * l1norm a := by
              unfold l1norm
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => ?_
              simp [abs_mul, abs_of_pos hcpos]
            rw [e1, abs_mul, abs_of_pos (inv_pos.mpr hcpos), ← mul_add, inv_mul_le_iff₀ hcpos]
            linarith
          have := h _ _ hle
          simp only [hscale, ENNReal.ofReal_mul (inv_nonneg.mpr hcpos.le)] at this
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at this
          exact (ENNReal.mul_le_mul_iff_right (by simpa using hcpos) ENNReal.ofReal_ne_top).1 this
        have hpt0 : ∀ t : ℝ, 0 ≤ t → ∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (max (t - s) 0) =
            ENNReal.ofReal (t ^ 2 / 2) := by
          intro t ht
          have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc 0 t ∪ Set.Ioi t := (Set.Ioc_union_Ioi_eq_Ioi ht).symm
          rw [hsplit, lintegral_union measurableSet_Ioi (Set.Ioc_disjoint_Ioi le_rfl)]
          have e2 : ∫⁻ s in Set.Ioi t, ENNReal.ofReal (max (t - s) 0) = 0 := by
            rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun _ => 0) (fun s hs => by
              simp only [Set.mem_Ioi] at hs
              rw [max_eq_right (by linarith)]; simp)]
            simp
          have e1 : ∫⁻ s in Set.Ioc 0 t, ENNReal.ofReal (max (t - s) 0) =
              ∫⁻ s in Set.Ioc 0 t, ENNReal.ofReal (t - s) := by
            refine setLIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
            rw [max_eq_left (by linarith [hs.2])]
          rw [e2, add_zero, e1, ← ofReal_integral_eq_lintegral_ofReal]
          · rw [← intervalIntegral.integral_of_le ht]
            congr 1
            rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id]
            simp
            ring
          · exact (continuous_const.sub continuous_id).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
          · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs => ?_)
            simp only [Pi.zero_apply]; linarith [hs.2]
        have hptneg : ∀ t : ℝ, t ≤ 0 → ∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (max (t - s) 0) = 0 := by
          intro t ht
          rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun _ => 0) (fun s hs => by
              simp only [Set.mem_Ioi] at hs
              rw [max_eq_right (by linarith)]; simp)]
          simp
        have hpt : ∀ t : ℝ, ENNReal.ofReal (t ^ 2) = 2 * ∫⁻ s in Set.Ioi (0 : ℝ),
            (ENNReal.ofReal (max (t - s) 0) + ENNReal.ofReal (max (-t - s) 0)) := by
          intro t
          rw [lintegral_add_left (by fun_prop)]
          rcases le_total 0 t with ht | ht
          · rw [hpt0 t ht, hptneg (-t) (by linarith), add_zero, ← ENNReal.ofReal_ofNat,
              ← ENNReal.ofReal_mul (by norm_num)]
            congr 1; ring
          · rw [hpt0 (-t) (by linarith), hptneg t ht, zero_add, ← ENNReal.ofReal_ofNat,
              ← ENNReal.ofReal_mul (by norm_num)]
            congr 1; ring
        have L3b : ∀ (μ : Measure ↥Ξ) [SFinite μ] (v : Pt d),
            ∫⁻ ξ, ENNReal.ofReal ((inner ℝ v (ξ : Pt d)) ^ 2) ∂μ =
              2 * ∫⁻ s in Set.Ioi (0 : ℝ), (∫⁻ ξ, ENNReal.ofReal (hinge v s (ξ : Pt d)) ∂μ +
                ∫⁻ ξ, ENNReal.ofReal (hinge (-v) s (ξ : Pt d)) ∂μ) := by
          intro μ _ v
          simp_rw [hpt]
          rw [lintegral_const_mul' _ _ (by simp)]
          congr 1
          rw [lintegral_lintegral_swap]
          · refine lintegral_congr fun s => ?_
            rw [← lintegral_add_left]
            · refine lintegral_congr fun ξ => ?_
              simp only [hinge, inner_neg_left]
            · unfold hinge; fun_prop
          · refine Continuous.aemeasurable ?_
            exact (ENNReal.continuous_ofReal.comp (by fun_prop)).add
              (ENNReal.continuous_ofReal.comp (by fun_prop))
        have L3 : ∀ (P Q : Measure ↥Ξ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q],
            ∫⁻ ξ, ENNReal.ofReal (‖(ξ : Pt d)‖ ^ 2) ∂P < ⊤ →
            ∫⁻ ξ, ENNReal.ofReal (‖(ξ : Pt d)‖ ^ 2) ∂Q ≤ ∫⁻ ξ, ENNReal.ofReal (‖(ξ : Pt d)‖ ^ 2) ∂P →
            (∀ (a : Pt d) (b : ℝ),
              ∫⁻ ξ, ENNReal.ofReal (hinge a b (ξ : Pt d)) ∂P ≤ ∫⁻ ξ, ENNReal.ofReal (hinge a b (ξ : Pt d)) ∂Q) →
            ∀ (v : Pt d) (s : ℝ),
              ∫⁻ ξ, ENNReal.ofReal (hinge v s (ξ : Pt d)) ∂P = ∫⁻ ξ, ENNReal.ofReal (hinge v s (ξ : Pt d)) ∂Q := by
          intro P Q _ _ hP hQP hle
          have hQ : ∫⁻ ξ, ENNReal.ofReal (‖(ξ : Pt d)‖ ^ 2) ∂Q < ⊤ := lt_of_le_of_lt hQP hP
          have key : ∀ x y z w : ENNReal, x ≤ y → z ≤ w → y + w ≤ x + z → x + z ≠ ⊤ → x = y := by
            intro x y z w hxy hzw h hfin
            refine le_antisymm hxy ?_
            by_contra hcon
            push Not at hcon
            have hz : z ≠ ⊤ := fun h' => hfin (by simp [h'])
            have h1 : x + z < y + z := ENNReal.add_lt_add_right hz hcon
            exact absurd (lt_of_lt_of_le h1 (add_le_add le_rfl hzw)) (not_lt.mpr h)
          obtain ⟨AA, hAA⟩ : ∃ AA : Measure ↥Ξ → Pt d → ENNReal, ∀ μ w,
              AA μ w = ∫⁻ ξ, ENNReal.ofReal ((inner ℝ w (ξ : Pt d)) ^ 2) ∂μ := ⟨_, fun _ _ => rfl⟩
          have hsq : ∀ w : Pt d, AA P w ≤ AA Q w := by
            intro w
            rw [hAA, hAA, L3b P w, L3b Q w]
            exact mul_le_mul_right (lintegral_mono fun s => add_le_add (hle w s) (hle (-w) s)) 2
          have hmeas : ∀ w : Pt d, Measurable fun ξ : ↥Ξ => ENNReal.ofReal ((inner ℝ w (ξ : Pt d)) ^ 2) := by
            intro w
            exact ENNReal.measurable_ofReal.comp (Continuous.measurable (by fun_prop))
          have hsos : ∀ (a : Pt d) (ξ : Pt d), 2 * (‖a‖ ^ 2 * ‖ξ‖ ^ 2) = 2 * (inner ℝ a ξ) ^ 2 +
              ∑ i, ∑ j, (inner ℝ (a i • EuclideanSpace.single j (1 : ℝ) - a j • EuclideanSpace.single i (1 : ℝ)) ξ) ^ 2 := by
            intro a ξ
            have e1 : ‖a‖ ^ 2 = ∑ i, a i ^ 2 := by
              rw [EuclideanSpace.norm_sq_eq]; simp
            have e2 : ‖ξ‖ ^ 2 = ∑ i, ξ i ^ 2 := by
              rw [EuclideanSpace.norm_sq_eq]; simp
            have e3 : inner ℝ a ξ = ∑ i, a i * ξ i := by
              rw [PiLp.inner_apply]; simp [mul_comm]
            have e4 : ∀ i j, inner ℝ (a i • EuclideanSpace.single j (1 : ℝ) - a j • EuclideanSpace.single i (1 : ℝ)) ξ
                = a i * ξ j - a j * ξ i := by
              intro i j
              rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left,
                EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_left]
              simp
            simp only [e4]
            have e5 : ∀ i j, (a i * ξ j - a j * ξ i) ^ 2 =
                a i ^ 2 * ξ j ^ 2 + ξ i ^ 2 * a j ^ 2 - 2 * ((a i * ξ i) * (a j * ξ j)) := by
              intro i j; ring
            simp only [e5, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
            rw [e1, e2, e3]
            ring
          have hlin : ∀ (μ : Measure ↥Ξ) (a : Pt d), ENNReal.ofReal (2 * ‖a‖ ^ 2) *
              ∫⁻ ξ, ENNReal.ofReal (‖(ξ : Pt d)‖ ^ 2) ∂μ =
              2 * AA μ a + ∑ i, ∑ j, AA μ (a i • EuclideanSpace.single j (1 : ℝ) - a j • EuclideanSpace.single i (1 : ℝ)) := by
            intro μ a
            have hm2 : Measurable fun ξ : ↥Ξ => ENNReal.ofReal (‖(ξ : Pt d)‖ ^ 2) :=
              ENNReal.measurable_ofReal.comp (Continuous.measurable (by fun_prop))
            rw [← lintegral_const_mul _ hm2]
            simp only [hAA]
            rw [← lintegral_const_mul _ (hmeas a)]
            simp_rw [← lintegral_finsetSum _ (fun j _ => hmeas _)]
            rw [← lintegral_finsetSum _ (fun i _ => Finset.measurable_sum _ (fun j _ => hmeas _)),
              ← lintegral_add_left ((hmeas a).const_mul _)]
            refine lintegral_congr fun ξ => ?_
            rw [← ENNReal.ofReal_mul (by positivity), mul_assoc, hsos a ξ,
              ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _),
              ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
              ENNReal.ofReal_sum_of_nonneg (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)]
            simp_rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
          have hAeq : ∀ a : Pt d, AA P a = AA Q a ∧ AA P a < ⊤ := by
            intro a
            have e1 := hlin P a
            have e2 := hlin Q a
            have hB : ∑ i, ∑ j, AA P (a i • EuclideanSpace.single j (1 : ℝ) - a j • EuclideanSpace.single i (1 : ℝ)) ≤
                ∑ i, ∑ j, AA Q (a i • EuclideanSpace.single j (1 : ℝ) - a j • EuclideanSpace.single i (1 : ℝ)) :=
              Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hsq _
            have hfin : 2 * AA P a + ∑ i, ∑ j, AA P (a i • EuclideanSpace.single j (1 : ℝ) - a j • EuclideanSpace.single i (1 : ℝ)) ≠ ⊤ := by
              rw [← e1]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hP.ne
            have h2 : 2 * AA Q a + ∑ i, ∑ j, AA Q (a i • EuclideanSpace.single j (1 : ℝ) - a j • EuclideanSpace.single i (1 : ℝ)) ≤
                2 * AA P a + ∑ i, ∑ j, AA P (a i • EuclideanSpace.single j (1 : ℝ) - a j • EuclideanSpace.single i (1 : ℝ)) := by
              rw [← e1, ← e2]; gcongr
            have h3 := key _ _ _ _ (by gcongr; exact hsq a) hB h2 hfin
            refine ⟨(ENNReal.mul_right_inj two_ne_zero ENNReal.ofNat_ne_top).1 h3, ?_⟩
            have : AA P a ≤ 2 * AA P a + ∑ i, ∑ j, AA P (a i • EuclideanSpace.single j (1 : ℝ) - a j • EuclideanSpace.single i (1 : ℝ)) := by
              calc AA P a ≤ 2 * AA P a := by
                    calc AA P a = 1 * AA P a := (one_mul _).symm
                      _ ≤ 2 * AA P a := by gcongr; norm_num
                _ ≤ _ := le_self_add
            exact lt_of_le_of_lt this (lt_top_iff_ne_top.2 hfin)
          have hint : ∀ (μ : Measure ↥Ξ) [IsProbabilityMeasure μ], ∫⁻ ξ, ENNReal.ofReal (‖(ξ : Pt d)‖ ^ 2) ∂μ < ⊤ →
              ∀ (v : Pt d) (s : ℝ), Integrable (fun ξ : ↥Ξ => hinge v s (ξ : Pt d)) μ := by
            intro μ _ hμ v s
            have h2 : Integrable (fun ξ : ↥Ξ => ‖(ξ : Pt d)‖ ^ 2) μ := by
              refine ⟨Continuous.aestronglyMeasurable (by fun_prop), ?_⟩
              rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ξ => by positivity)]
              exact hμ
            refine Integrable.mono' ((h2.const_mul ‖v‖).add (integrable_const (‖v‖ + |s|)))
              (Continuous.aestronglyMeasurable (by unfold hinge; fun_prop)) (Eventually.of_forall fun ξ => ?_)
            have h0 : 0 ≤ hinge v s (ξ : Pt d) := le_max_right _ _
            rw [Real.norm_eq_abs, abs_of_nonneg h0]
            have hi := (abs_le.mp (abs_real_inner_le_norm v (ξ : Pt d))).2
            have h1 : ‖(ξ : Pt d)‖ ≤ 1 + ‖(ξ : Pt d)‖ ^ 2 := by nlinarith [norm_nonneg (ξ : Pt d)]
            have h3 := mul_le_mul_of_nonneg_left h1 (norm_nonneg v)
            have h4 := neg_abs_le s
            show hinge v s (ξ : Pt d) ≤ ‖v‖ * ‖(ξ : Pt d)‖ ^ 2 + (‖v‖ + |s|)
            unfold hinge
            apply max_le
            · nlinarith [norm_nonneg v, abs_nonneg s]
            · nlinarith [norm_nonneg v, abs_nonneg s, sq_nonneg ‖(ξ : Pt d)‖]
          have hofr : ∀ (μ : Measure ↥Ξ) [IsProbabilityMeasure μ], ∫⁻ ξ, ENNReal.ofReal (‖(ξ : Pt d)‖ ^ 2) ∂μ < ⊤ →
              ∀ (v : Pt d) (s : ℝ), ∫⁻ ξ, ENNReal.ofReal (hinge v s (ξ : Pt d)) ∂μ =
                ENNReal.ofReal (∫ ξ, hinge v s (ξ : Pt d) ∂μ) := by
            intro μ _ hμ v s
            rw [ofReal_integral_eq_lintegral_ofReal (hint μ hμ v s) (Eventually.of_forall fun ξ => le_max_right _ _)]
          have hcont : ∀ (μ : Measure ↥Ξ) [IsProbabilityMeasure μ], ∫⁻ ξ, ENNReal.ofReal (‖(ξ : Pt d)‖ ^ 2) ∂μ < ⊤ →
              ∀ v : Pt d, Continuous fun s => ∫ ξ, hinge v s (ξ : Pt d) ∂μ := by
            intro μ _ hμ v
            refine (LipschitzWith.of_dist_le_mul (K := 1) fun s t => ?_).continuous
            rw [Real.dist_eq, ← integral_sub (hint μ hμ v s) (hint μ hμ v t)]
            have hb : ∀ ξ : ↥Ξ, ‖hinge v s (ξ : Pt d) - hinge v t (ξ : Pt d)‖ ≤ |s - t| := by
              intro ξ
              rw [Real.norm_eq_abs]; unfold hinge
              have h1 := abs_max_sub_max_le_abs (inner ℝ v (ξ : Pt d) - s) (inner ℝ v (ξ : Pt d) - t) 0
              have e : (inner ℝ v (ξ : Pt d) - s) - (inner ℝ v (ξ : Pt d) - t) = -(s - t) := by ring
              rw [e, abs_neg] at h1
              exact h1
            have := norm_integral_le_of_norm_le_const (μ := μ) (Eventually.of_forall hb)
            simpa [Real.dist_eq] using this
          have hle' : ∀ (a : Pt d) (b : ℝ), ENNReal.ofReal (∫ ξ, hinge a b (ξ : Pt d) ∂P) ≤
              ENNReal.ofReal (∫ ξ, hinge a b (ξ : Pt d) ∂Q) := by
            intro a b
            rw [← hofr P hP, ← hofr Q hQ]
            exact hle a b
          have hpos : ∀ v : Pt d, ∀ s : ℝ, 0 ≤ s →
              ∫ ξ, hinge v s (ξ : Pt d) ∂P = ∫ ξ, hinge v s (ξ : Pt d) ∂Q := by
            intro v
            obtain ⟨hA, hAfin⟩ := hAeq v
            rw [hAA, hAA, L3b P v, L3b Q v] at hA
            rw [hAA, L3b P v] at hAfin
            have hI := (ENNReal.mul_right_inj two_ne_zero ENNReal.ofNat_ne_top).1 hA
            have hIfin : ∫⁻ s in Set.Ioi (0:ℝ), (∫⁻ ξ, ENNReal.ofReal (hinge v s (ξ : Pt d)) ∂P +
                ∫⁻ ξ, ENNReal.ofReal (hinge (-v) s (ξ : Pt d)) ∂P) ≠ ⊤ := by
              intro h; rw [h] at hAfin; simp at hAfin
            simp only [hofr P hP, hofr Q hQ] at hI hIfin
            have hae := ae_eq_of_ae_le_of_lintegral_le (μ := volume.restrict (Set.Ioi (0:ℝ)))
              (Eventually.of_forall fun s => add_le_add (hle' v s) (hle' (-v) s)) hIfin
              ((ENNReal.measurable_ofReal.comp (hcont Q hQ v).measurable).add
                (ENNReal.measurable_ofReal.comp (hcont Q hQ (-v)).measurable)).aemeasurable hI.ge
            have hae2 : ∀ᵐ s ∂(volume.restrict (Set.Ioi (0:ℝ))),
                ∫ ξ, hinge v s (ξ : Pt d) ∂P = ∫ ξ, hinge v s (ξ : Pt d) ∂Q := by
              filter_upwards [hae] with s hs
              have hfs : ENNReal.ofReal (∫ ξ, hinge v s (ξ : Pt d) ∂P) +
                  ENNReal.ofReal (∫ ξ, hinge (-v) s (ξ : Pt d) ∂P) ≠ ⊤ :=
                ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
              have := key _ _ _ _ (hle' v s) (hle' (-v) s) hs.symm.le hfs
              exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun _ => le_max_right _ _)
                (integral_nonneg fun _ => le_max_right _ _)).1 this
            have heq := Measure.eqOn_open_of_ae_eq hae2 isOpen_Ioi (hcont P hP v).continuousOn
              (hcont Q hQ v).continuousOn
            have hcl := closure_minimal heq (isClosed_eq (hcont P hP v) (hcont Q hQ v))
            rw [closure_Ioi] at hcl
            exact fun s hs => hcl hs
          intro v s
          rw [hofr P hP, hofr Q hQ]
          congr 1
          rcases le_or_gt 0 s with hs | hs
          · exact hpos v s hs
          · have hid : ∀ (μ : Measure ↥Ξ) [IsProbabilityMeasure μ],
                ∫⁻ ξ, ENNReal.ofReal (‖(ξ : Pt d)‖ ^ 2) ∂μ < ⊤ →
                ∫ ξ, hinge v s (ξ : Pt d) ∂μ = ∫ ξ, hinge v 0 (ξ : Pt d) ∂μ - ∫ ξ, hinge (-v) 0 (ξ : Pt d) ∂μ
                  - s + ∫ ξ, hinge (-v) (-s) (ξ : Pt d) ∂μ := by
              intro μ _ hμ
              have hpt : ∀ ξ : ↥Ξ, hinge v s (ξ : Pt d) = hinge v 0 (ξ : Pt d) - hinge (-v) 0 (ξ : Pt d)
                  - s + hinge (-v) (-s) (ξ : Pt d) := by
                intro ξ
                unfold hinge
                rw [inner_neg_left]
                simp only [max_def]
                split_ifs <;> linarith
              have e1 := integral_add (((hint μ hμ v 0).sub (hint μ hμ (-v) 0)).sub (integrable_const s))
                (hint μ hμ (-v) (-s))
              have e2 := integral_sub ((hint μ hμ v 0).sub (hint μ hμ (-v) 0)) (integrable_const s)
              have e3 := integral_sub (hint μ hμ v 0) (hint μ hμ (-v) 0)
              simp only [Pi.sub_apply, Pi.add_apply] at e1 e2 e3
              rw [integral_congr_ae (Eventually.of_forall hpt), e1, e2, e3]
              simp
            rw [hid P hP, hid Q hQ, hpos v 0 le_rfl, hpos (-v) 0 le_rfl, hpos (-v) (-s) (by linarith)]
        -- main assembly
        have hhc : ∀ (a : Pt d) (b : ℝ), Continuous (fun ξ : ↥Ξ => hinge a b (ξ : Pt d)) := by
          intro a b
          unfold hinge
          fun_prop
        have hh0 : ∀ (a : Pt d) (b : ℝ) (x : Pt d), 0 ≤ hinge a b x := fun a b x => le_max_right _ _
        have L0 : ∀ (μ : Measure ↥Ξ) [IsProbabilityMeasure μ],
            ∫⁻ ξ, ENNReal.ofReal (‖(ξ : Pt d)‖ ^ 2) ∂μ < ⊤ →
            ∀ (v : Pt d) (s : ℝ), Integrable (fun ξ : ↥Ξ => hinge v s (ξ : Pt d)) μ := by
          intro μ _ hμ v s
          have hsq : Integrable (fun ξ : ↥Ξ => ‖(ξ : Pt d)‖ ^ 2) μ := by
            refine ⟨by fun_prop, ?_⟩
            rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ξ => by positivity)]
            exact hμ
          refine Integrable.mono' (((hsq.const_mul ‖v‖).add (integrable_const ‖v‖)).add (integrable_const |s|))
            (hhc v s).aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
          rw [Real.norm_eq_abs, abs_of_nonneg (hh0 _ _ _)]
          have h1 : |inner ℝ v (ξ : Pt d)| ≤ ‖v‖ * ‖(ξ : Pt d)‖ := abs_real_inner_le_norm _ _
          have h2 : ‖(ξ : Pt d)‖ ≤ ‖(ξ : Pt d)‖ ^ 2 + 1 := by nlinarith [norm_nonneg (ξ : Pt d)]
          have h3 : ‖v‖ * ‖(ξ : Pt d)‖ ≤ ‖v‖ * (‖(ξ : Pt d)‖ ^ 2 + 1) :=
            mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
          unfold hinge
          simp only [Pi.add_apply]
          apply max_le
          · have := le_abs_self (inner ℝ v (ξ : Pt d)); have := neg_abs_le s; nlinarith
          · have := abs_nonneg s; positivity
        have hsampleSum : ∀ (f : ↥Ξ → ℝ) (ω : ℕ → ↥Ξ) (N : ℕ),
            (1 / (N : ℝ)) * ∑ i, f (sample ω N i) = (∑ i ∈ Finset.range N, f (ω i)) / N := by
          intro f ω N
          rw [Finset.sum_range, one_div, div_eq_inv_mul]
          rfl
        intro F F₀ hF₀ hne
        have hlin : ∀ (μ : Measure ↥Ξ) (a : Pt d) (b : ℝ), Integrable (fun ξ : ↥Ξ => hinge a b (ξ : Pt d)) μ →
            ∫⁻ ξ, ENNReal.ofReal (hinge a b (ξ : Pt d)) ∂μ =
              ENNReal.ofReal (∫ ξ, hinge a b (ξ : Pt d) ∂μ) := by
          intro μ a b hi
          rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun ξ => hh0 _ _ _)]
        by_cases hA : ∃ a b, l1norm a + |b| ≤ 1 ∧ hingeMean F a b < hingeMean F₀ a b
        · obtain ⟨a, b, hab, hlt⟩ := hA
          have hiF : Integrable (fun ξ : ↥Ξ => hinge a b (ξ : Pt d)) (F : Measure ↥Ξ) := by
            refine ⟨(hhc a b).aestronglyMeasurable, ?_⟩
            rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ξ => hh0 _ _ _)]
            exact lt_of_lt_of_le hlt le_top
          have hiF₀ : Integrable (fun ξ : ↥Ξ => hinge a b (ξ : Pt d)) (F₀ : Measure ↥Ξ) := L0 _ hF₀ a b
          set c := ∫ ξ, hinge a b (ξ : Pt d) ∂(F : Measure ↥Ξ) with hc
          set c0 := ∫ ξ, hinge a b (ξ : Pt d) ∂(F₀ : Measure ↥Ξ) with hc0
          have e1 : hingeMean F a b = ENNReal.ofReal c := hlin _ a b hiF
          have e0 : hingeMean F₀ a b = ENNReal.ofReal c0 := hlin _ a b hiF₀
          have hc0nn : 0 ≤ c0 := integral_nonneg fun ξ => hh0 _ _ _
          have hcc : c < c0 := by
            rw [e1, e0] at hlt
            exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (integral_nonneg fun ξ => hh0 _ _ _)).1 hlt
          refine L1 F (fun ξ => -hinge a b (ξ : Pt d)) (hhc a b).neg hiF.neg (fun N => QC N - c0) (-c0)
            (by simpa using hQC.sub_const c0) (by rw [integral_neg]; linarith) _ ?_
          intro N ω hω
          obtain ⟨h1, -⟩ := hω
          have h2 : ((hingeMean F₀ a b : ENNReal) : EReal) -
              (((1 / (N : ℝ)) * ∑ i, hinge a b ((sample ω N i : ↥Ξ) : Pt d) : ℝ) : EReal) ≤ (QC N : EReal) := by
            refine le_trans ?_ h1
            unfold lcxStat
            exact le_iSup_of_le a (le_iSup_of_le b (le_iSup_of_le hab le_rfl))
          rw [e0, EReal.coe_ennreal_ofReal, max_eq_left hc0nn, ← EReal.coe_sub, EReal.coe_le_coe_iff,
            hsampleSum (fun ξ => hinge a b (ξ : Pt d))] at h2
          simp only [Set.mem_setOf_eq, Finset.sum_neg_distrib, neg_div]
          linarith
        by_cases hB : secondMoment F₀ < secondMoment F
        · have hcn : Continuous fun ξ : ↥Ξ => ‖(ξ : Pt d)‖ ^ 2 := by fun_prop
          have hsup : secondMoment F = ⨆ n : ℕ, ∫⁻ ξ, ENNReal.ofReal (min (‖(ξ : Pt d)‖ ^ 2) n) ∂(F : Measure ↥Ξ) := by
            unfold secondMoment
            rw [← lintegral_iSup]
            · congr 1
              ext ξ
              refine le_antisymm ?_ (iSup_le fun n => ENNReal.ofReal_le_ofReal (min_le_left _ _))
              obtain ⟨n, hn⟩ := exists_nat_ge (‖(ξ : Pt d)‖ ^ 2)
              exact le_iSup_of_le n (le_of_eq (by rw [min_eq_left hn]))
            · intro n
              exact ENNReal.measurable_ofReal.comp ((hcn.min continuous_const).measurable)
            · intro m n hmn ξ
              exact ENNReal.ofReal_le_ofReal (min_le_min_left _ (by exact_mod_cast hmn))
          rw [hsup] at hB
          obtain ⟨M, hM⟩ := lt_iSup_iff.1 hB
          set s0 := (secondMoment F₀).toReal with hs0
          have hs0e : secondMoment F₀ = ENNReal.ofReal s0 := (ENNReal.ofReal_toReal hF₀.ne).symm
          have hs0nn : 0 ≤ s0 := ENNReal.toReal_nonneg
          have hgc : Continuous fun ξ : ↥Ξ => min (‖(ξ : Pt d)‖ ^ 2) (M : ℝ) := hcn.min continuous_const
          have hgi : Integrable (fun ξ : ↥Ξ => min (‖(ξ : Pt d)‖ ^ 2) (M : ℝ)) (F : Measure ↥Ξ) := by
            refine Integrable.mono' (integrable_const (M : ℝ)) hgc.aestronglyMeasurable
              (Eventually.of_forall fun ξ => ?_)
            rw [Real.norm_eq_abs, abs_of_nonneg (le_min (by positivity) (Nat.cast_nonneg _))]
            exact min_le_right _ _
          have hgnn : ∀ ξ : ↥Ξ, 0 ≤ min (‖(ξ : Pt d)‖ ^ 2) (M : ℝ) :=
            fun ξ => le_min (by positivity) (Nat.cast_nonneg _)
          rw [← ofReal_integral_eq_lintegral_ofReal hgi (Eventually.of_forall hgnn), hs0e,
            ENNReal.ofReal_lt_ofReal_iff_of_nonneg hs0nn] at hM
          refine L1 F (fun ξ => min (‖(ξ : Pt d)‖ ^ 2) (M : ℝ)) hgc hgi (fun N => s0 + QR N) s0
            (by simpa using hQR.const_add s0) hM _ ?_
          intro N ω hω
          obtain ⟨-, h2⟩ := hω
          rw [hs0e, EReal.coe_ennreal_ofReal, max_eq_left hs0nn, EReal.coe_le_coe_iff] at h2
          unfold empSecondMoment at h2
          rw [hsampleSum (fun ξ => ‖(ξ : Pt d)‖ ^ 2)] at h2
          simp only [Set.mem_ofPred_eq]
          have h3 : (∑ i ∈ Finset.range N, min (‖((ω i : ↥Ξ) : Pt d)‖ ^ 2) (M : ℝ)) / N ≤
              (∑ i ∈ Finset.range N, ‖((ω i : ↥Ξ) : Pt d)‖ ^ 2) / N :=
            div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => min_le_left _ _) (Nat.cast_nonneg _)
          linarith
        · exfalso
          apply hne
          push_neg at hA hB
          have hall := L3a _ _ hA
          have heq := L3 (F₀ : Measure ↥Ξ) (F : Measure ↥Ξ) hF₀ hB hall
          have hF2 : ∫⁻ ξ, ENNReal.ofReal (‖(ξ : Pt d)‖ ^ 2) ∂(F : Measure ↥Ξ) < ⊤ := lt_of_le_of_lt hB hF₀
          have h := L2 (F₀ : Measure ↥Ξ) (F : Measure ↥Ξ) (L0 _ hF₀) (L0 _ hF2) (by
            intro v s
            have := heq v s
            rw [hlin _ v s (L0 _ hF₀ v s), hlin _ v s (L0 _ hF2 v s)] at this
            exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun ξ => hh0 _ _ _)
              (integral_nonneg fun ξ => hh0 _ _ _)).1 this)
          exact Subtype.ext h
