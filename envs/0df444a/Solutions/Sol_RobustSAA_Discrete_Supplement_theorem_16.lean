-- Prove2me | solution 1 for RobustSAA.Discrete.Supplement.theorem_16
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:16:35.970879+00:00
-- url     : https://prove2.me/submissions/032392f2-817e-414c-93c8-9e9986a29d39

import Mathlib
import Definitions.Def_RobustSAA_Convergence_Setting
import Definitions.Def_RobustSAA_Discrete_Supplement_LCX

open RobustSAA
open RobustSAA.Discrete
open RobustSAA.Discrete.Supplement

open MeasureTheory Filter Topology RobustSAA.Convergence
open scoped ENNReal

theorem solution {d N : ℕ} (hN : 2 ≤ N) (hdN : d + 1 ≤ N) (Ξ : Set (Pt d))
    (hΞ : IsClosed Ξ) (F F₀ : ProbabilityMeasure ↥Ξ) (hLCX : LCXle F₀ F)
    (α₁ α₂ : ℝ) (hα₁ : 0 < α₁ ∧ α₁ < 1) (hα₂ : 0 ≤ α₂) (Qbar : (Fin N → ↥Ξ) → ℝ)
    (hQbar : dataLaw F {ω | ¬ (((secondMoment F : ℝ≥0∞) : EReal) ≤
        ((Qbar (sample ω N) : ℝ) : EReal))} ≤ ENNReal.ofReal α₂) :
    (1 < pExp N ∧ pExp N < 2) ∧
    dataLaw F {ω | ¬ (((secondMoment F : ℝ≥0∞) : EReal) ≤ ((Qbar (sample ω N) : ℝ) : EReal) ∧
        lcxStat F₀ (sample ω N) ≤ ((lcxThreshold d N α₁ (Qbar (sample ω N)) : ℝ) : EReal))} ≤
      ENNReal.ofReal (α₁ + α₂) ∧
    ∀ B : ℝ, ((secondMoment F : ℝ≥0∞) : EReal) ≤ (B : EReal) →
      dataLaw F {ω | ¬ (lcxStat F₀ (sample ω N) ≤ ((lcxThreshold d N α₁ B : ℝ) : EReal))} ≤
        ENNReal.ofReal α₁ := by
          have hpE : ∀ N : ℕ, 2 ≤ N → 1 < pExp N ∧ pExp N < 2 ∧
              (Real.log (2 * N) + 3) / 2 ≤ 1 + pExp N / (2 - pExp N) := by
            intro N hN
            have hN' : (2:ℝ) ≤ N := by exact_mod_cast hN
            have hL : Real.log 256 + 8 * Real.log N = 8 * Real.log (2 * N) := by
              rw [Real.log_mul (by norm_num) (by linarith), show (256:ℝ) = 2 ^ 8 by norm_num,
                Real.log_pow]; push_cast; ring
            have hL1 : 1 < Real.log (2 * N) := by
              have h4 : Real.log 4 ≤ Real.log (2 * N) := Real.log_le_log (by norm_num) (by linarith)
              have : Real.log 4 = 2 * Real.log 2 := by
                rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
              linarith [Real.log_two_gt_d9]
            unfold pExp
            rw [hL]
            set L := Real.log (2 * N)
            have hr0 : 0 ≤ Real.sqrt (8 * L + L ^ 2) := Real.sqrt_nonneg _
            have hr2 : Real.sqrt (8 * L + L ^ 2) ^ 2 = 8 * L + L ^ 2 := Real.sq_sqrt (by have := sq_nonneg L; linarith)
            set r := Real.sqrt (8 * L + L ^ 2)
            have hr1 : L + 2 < r := lt_of_pow_lt_pow_left₀ 2 hr0 (by rw [hr2]; linarith)
            have hr3 : r < L + 4 := lt_of_pow_lt_pow_left₀ 2 (by linarith) (by rw [hr2]; linarith)
            have h2p : 0 < 2 - 1 / 2 * (r - L) := by linarith
            refine ⟨by linarith, by linarith, ?_⟩
            rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
            have : 1 + 1 / 2 * (r - L) / (2 - 1 / 2 * (r - L)) = 2 / (2 - 1 / 2 * (r - L)) := by
              rw [one_add_div h2p.ne']; congr 1; ring
            rw [this, div_mul_eq_mul_div, le_div_iff₀ h2p]
            have := mul_pos (sub_pos.2 hr3) (sub_pos.2 hr1)
            linarith
          have hnum : ∀ (N : ℕ) (n α : ℝ), 2 ≤ N → 1 ≤ n → n ≤ N → 0 < α → α < 1 →
              2 * Real.sqrt n / N + Real.sqrt (2 * (n * Real.log (2 * N + 1) + Real.log (1 / α)) / N) ≤
              (1 + pExp N / (2 - pExp N)) * ((2 : ℝ) ^ (1 / 2 + 1 / pExp N) / (N : ℝ) ^ (1 - 1 / pExp N)) *
                Real.sqrt (n + n * Real.log (N / n) + Real.log (4 / α)) := by
            intro N n α hN hn hnN hα0 hα1
            obtain ⟨hp1, hp2, hp3⟩ := hpE N hN
            have hN' : (2:ℝ) ≤ N := by exact_mod_cast hN
            set p := pExp N
            set L := Real.log (2 * N)
            have hlogα : 0 ≤ Real.log (1 / α) := Real.log_nonneg (by rw [le_div_iff₀ hα0]; linarith)
            have hlog4 : Real.log (4 / α) = Real.log 4 + Real.log (1 / α) := by
              rw [← Real.log_mul (by norm_num) (by positivity)]; ring_nf
            have hlog4' : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
            have hlogNn : 0 ≤ Real.log (N / n) := Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
            set A := n + Real.log (1 / α)
            have hAS : A ≤ n + n * Real.log (N / n) + Real.log (4 / α) := by
              have : 0 ≤ n * Real.log (N / n) := by positivity
              linarith
            have hc1 : 1 ≤ Real.log (2 * N + 1) := by
              rw [Real.le_log_iff_exp_le (by positivity)]
              linarith [Real.exp_one_lt_d9]
            have hcL : Real.log (2 * N + 1) ≤ L + 1 := by
              have : Real.log (2 * N + 1) ≤ Real.log (2 * (2 * N)) := Real.log_le_log (by positivity) (by linarith)
              rw [Real.log_mul (by norm_num) (by positivity)] at this
              linarith [Real.log_two_lt_d9]
            set c := Real.log (2 * N + 1)
            have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
            -- lower bound on the middle factor
            have hNpos : (0:ℝ) < N := by linarith
            have hmid : 2 / Real.sqrt N ≤ (2 : ℝ) ^ (1 / 2 + 1 / p) / (N : ℝ) ^ (1 - 1 / p) := by
              have h1 : (2:ℝ) ≤ (2 : ℝ) ^ (1 / 2 + 1 / p) := by
                calc (2:ℝ) = 2 ^ (1:ℝ) := (Real.rpow_one 2).symm
                  _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
                    have : 1 / 2 ≤ 1 / p := by rw [div_le_div_iff₀ (by norm_num) (by linarith)]; linarith
                    linarith)
              have h2 : (N : ℝ) ^ (1 - 1 / p) ≤ Real.sqrt N := by
                rw [Real.sqrt_eq_rpow]
                apply Real.rpow_le_rpow_of_exponent_le (by linarith)
                have : 1 / 2 ≤ 1 / p := by rw [div_le_div_iff₀ (by norm_num) (by linarith)]; linarith
                linarith
              have h3 : 0 < (N : ℝ) ^ (1 - 1 / p) := Real.rpow_pos_of_pos hNpos _
              calc 2 / Real.sqrt N ≤ 2 / (N : ℝ) ^ (1 - 1 / p) := div_le_div_of_nonneg_left (by norm_num) h3 h2
                _ ≤ _ := div_le_div_of_nonneg_right h1 h3.le
            have hsN : Real.sqrt 2 ≤ Real.sqrt N := Real.sqrt_le_sqrt hN'
            have hsNpos : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNpos
            have hsN2 : Real.sqrt N ^ 2 = N := Real.sq_sqrt hNpos.le
            have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
            have hs2pos : 0 < Real.sqrt 2 := by positivity
            have hsA : 0 ≤ Real.sqrt A := Real.sqrt_nonneg _
            have hsAS : Real.sqrt A ≤ Real.sqrt (n + n * Real.log (N / n) + Real.log (4 / α)) := Real.sqrt_le_sqrt hAS
            have hsn : Real.sqrt n ≤ Real.sqrt A := Real.sqrt_le_sqrt (by linarith)
            have hsc : Real.sqrt c ≤ (L + 2) / 2 := by
              rw [Real.sqrt_le_left (by linarith)]; linarith [sq_nonneg L]
            -- term 1
            have ht1 : 2 * Real.sqrt n / N ≤ Real.sqrt 2 * Real.sqrt A / Real.sqrt N := by
              rw [div_le_div_iff₀ (by positivity) hsNpos]
              have : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
              calc 2 * Real.sqrt n * Real.sqrt N = Real.sqrt 2 * Real.sqrt 2 * Real.sqrt n * Real.sqrt N := by
                    rw [← sq, hs2]
                _ ≤ Real.sqrt 2 * Real.sqrt N * Real.sqrt A * Real.sqrt N := by gcongr
                _ = Real.sqrt 2 * Real.sqrt A * N := by linear_combination (Real.sqrt 2 * Real.sqrt A) * hsN2
            have ht2 : Real.sqrt (2 * (n * c + Real.log (1 / α)) / N) ≤
                Real.sqrt 2 * Real.sqrt c * Real.sqrt A / Real.sqrt N := by
              rw [Real.sqrt_le_left (by positivity), div_pow, mul_pow, mul_pow, hs2, hsN2,
                Real.sq_sqrt (by linarith), Real.sq_sqrt (by positivity)]
              apply div_le_div_of_nonneg_right _ hNpos.le
              have hA : A = n + Real.log (1 / α) := rfl
              rw [hA]
              linarith [mul_le_mul_of_nonneg_right hc1 hlogα]
            calc _ ≤ Real.sqrt 2 * Real.sqrt A / Real.sqrt N + Real.sqrt 2 * Real.sqrt c * Real.sqrt A / Real.sqrt N := add_le_add ht1 ht2
              _ = (Real.sqrt 2 * (1 + Real.sqrt c)) * Real.sqrt A / Real.sqrt N := by ring
              _ ≤ ((L + 3) / 2) * (2 / Real.sqrt N) * Real.sqrt A := by
                  have : Real.sqrt 2 ≤ 1.415 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
                  have key : Real.sqrt 2 * (1 + Real.sqrt c) ≤ L + 3 := by
                    have h5 := mul_le_mul_of_nonneg_right this
                      (show 0 ≤ 1 + Real.sqrt c by have := Real.sqrt_nonneg c; linarith)
                    linarith
                  calc (Real.sqrt 2 * (1 + Real.sqrt c)) * Real.sqrt A / Real.sqrt N
                      = (Real.sqrt 2 * (1 + Real.sqrt c)) * (Real.sqrt A / Real.sqrt N) := by ring
                    _ ≤ (L + 3) * (Real.sqrt A / Real.sqrt N) := mul_le_mul_of_nonneg_right key (by positivity)
                    _ = _ := by ring
              _ ≤ _ := by gcongr
          have hexp : ∀ y : ℝ, 0 ≤ y → Real.exp (-y) ≤ 1 - y + y ^ 2 / 2 := by
            intro y hy
            have h1 := Real.quadratic_le_exp_of_nonneg hy
            have h2 : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
            have h3 : 0 < Real.exp (-y) := Real.exp_pos _
            have h4 : 0 ≤ 1 - y + y ^ 2 / 2 := by linarith [sq_nonneg (y - 1)]
            have h5 : Real.exp (-y) * (1 - y + y ^ 2 / 2) * Real.exp y = 1 - y + y ^ 2 / 2 := by
              rw [mul_right_comm, h2, one_mul]
            have h6 := mul_nonneg h3.le (sq_nonneg (y ^ 2))
            have h7 := mul_le_mul_of_nonneg_left h1 (mul_nonneg h3.le h4)
            linarith
          have hChern : ∀ (g : ↥Ξ → ℝ), Measurable g → (∀ x, 0 ≤ g x) →
              Integrable g (F : Measure ↥Ξ) → Integrable (fun x => g x ^ 2) (F : Measure ↥Ξ) →
              ∀ (W t : ℝ), 0 < W → 0 ≤ t → ∫ x, g x ^ 2 ∂(F : Measure ↥Ξ) ≤ W →
              dataLaw F {ω | ∑ i ∈ Finset.range N, g (ω i) ≤ N * (∫ x, g x ∂(F : Measure ↥Ξ) - t)} ≤
                ENNReal.ofReal (Real.exp (-(N * t ^ 2 / (2 * W)))) := by
            clear hpE hnum hQbar Qbar hLCX
            intro g hg hg0 hgi hg2 W t hW ht hgW
            set μ : Measure ↥Ξ := (F : Measure ↥Ξ)
            set P := dataLaw F
            have hP : P = Measure.infinitePi (fun _ : ℕ => μ) := rfl
            have : IsProbabilityMeasure P := by rw [hP]; infer_instance
            set X : ℕ → (ℕ → ↥Ξ) → ℝ := fun i ω => g (ω i) with hX
            have hind : ProbabilityTheory.iIndepFun X P := by
              rw [hP]; exact ProbabilityTheory.iIndepFun_infinitePi (X := fun _ => g) (fun _ => hg)
            have hXm : ∀ i, Measurable (X i) := fun i => hg.comp (measurable_pi_apply i)
            set l := t / W with hl
            have hl0 : 0 ≤ l := div_nonneg ht hW.le
            have hmgf1 : ∀ i, ProbabilityTheory.mgf (X i) P (-l) = ProbabilityTheory.mgf g μ (-l) := by
              intro i
              simp only [ProbabilityTheory.mgf, hX]
              have hmp := measurePreserving_eval_infinitePi (fun _ : ℕ => μ) i
              have hae : AEStronglyMeasurable (fun x => Real.exp (-l * g x))
                  (Measure.map (Function.eval i) (Measure.infinitePi (fun _ : ℕ => μ))) := by
                rw [hmp.map_eq]
                exact (Real.continuous_exp.measurable.comp (measurable_const.mul hg)).aestronglyMeasurable
              rw [hP, ← integral_map hmp.measurable.aemeasurable hae, hmp.map_eq]
            have hmgfg : ProbabilityTheory.mgf g μ (-l) ≤ Real.exp (-l * ∫ x, g x ∂μ + l ^ 2 * W / 2) := by
              have hint : Integrable (fun x => Real.exp (-l * g x)) μ := by
                refine Integrable.of_bound
                  (Real.continuous_exp.measurable.comp (measurable_const.mul hg)).aestronglyMeasurable 1
                  (ae_of_all _ fun x => ?_)
                rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
                rw [Real.exp_le_one_iff]; have := mul_nonneg hl0 (hg0 x); linarith
              have hint2 : Integrable (fun x => 1 - l * g x + l ^ 2 / 2 * g x ^ 2) μ :=
                ((integrable_const 1).sub (hgi.const_mul l)).add (hg2.const_mul _)
              calc ProbabilityTheory.mgf g μ (-l) = ∫ x, Real.exp (-l * g x) ∂μ := rfl
                _ ≤ ∫ x, (1 - l * g x + l ^ 2 / 2 * g x ^ 2) ∂μ := by
                  refine integral_mono hint hint2 fun x => ?_
                  have := hexp (l * g x) (mul_nonneg hl0 (hg0 x))
                  simp only [neg_mul]; linarith
                _ = 1 - l * ∫ x, g x ∂μ + l ^ 2 / 2 * ∫ x, g x ^ 2 ∂μ := by
                  have ha : Integrable (fun x => 1 - l * g x) μ := (integrable_const 1).sub (hgi.const_mul l)
                  have hb : Integrable (fun x => l ^ 2 / 2 * g x ^ 2) μ := hg2.const_mul _
                  have hc : Integrable (fun x => l * g x) μ := hgi.const_mul l
                  rw [integral_add ha hb, integral_sub (integrable_const 1) hc, integral_const_mul,
                    integral_const_mul]
                  simp
                _ ≤ 1 + (-l * ∫ x, g x ∂μ + l ^ 2 * W / 2) := by
                  have : l ^ 2 / 2 * ∫ x, g x ^ 2 ∂μ ≤ l ^ 2 / 2 * W :=
                    mul_le_mul_of_nonneg_left hgW (by positivity)
                  linarith
                _ ≤ _ := by linarith [Real.add_one_le_exp (-l * ∫ x, g x ∂μ + l ^ 2 * W / 2)]
            have hmgf0 : 0 ≤ ProbabilityTheory.mgf g μ (-l) := ProbabilityTheory.mgf_nonneg
            set Y := ∑ i ∈ Finset.range N, X i with hY
            have hYm : Measurable Y := by
              have : Y = fun ω => ∑ i ∈ Finset.range N, X i ω := by
                ext ω; simp only [hY, Finset.sum_apply]
              rw [this]; exact Finset.measurable_sum _ fun i _ => hXm i
            have hYeq : ∀ ω, Y ω = ∑ i ∈ Finset.range N, g (ω i) := fun ω => by
              simp only [hY, Finset.sum_apply, hX]
            have hYint : Integrable (fun ω => Real.exp (-l * Y ω)) P := by
              refine Integrable.of_bound
                (Real.continuous_exp.measurable.comp (measurable_const.mul hYm)).aestronglyMeasurable 1
                (ae_of_all _ fun ω => ?_)
              rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, hYeq]
              have : 0 ≤ ∑ i ∈ Finset.range N, g (ω i) := Finset.sum_nonneg fun i _ => hg0 _
              have := mul_nonneg hl0 this
              linarith
            have hmain := ProbabilityTheory.measure_le_le_exp_mul_mgf (X := Y) (μ := P) (N * (∫ x, g x ∂μ - t))
              (by linarith : -l ≤ 0) hYint
            rw [hind.mgf_sum hXm, Finset.prod_congr rfl (fun i _ => hmgf1 i), Finset.prod_const,
              Finset.card_range] at hmain
            have hset : {ω | ∑ i ∈ Finset.range N, g (ω i) ≤ N * (∫ x, g x ∂μ - t)} =
                {ω | Y ω ≤ N * (∫ x, g x ∂μ - t)} := by
              ext ω; simp only [Set.mem_ofPred_eq, hYeq]
            rw [hset, ← ofReal_measureReal]
            apply ENNReal.ofReal_le_ofReal
            refine hmain.trans ?_
            calc Real.exp (- -l * (N * (∫ x, g x ∂μ - t))) * ProbabilityTheory.mgf g μ (-l) ^ N
                ≤ Real.exp (- -l * (N * (∫ x, g x ∂μ - t))) *
                  Real.exp (-l * ∫ x, g x ∂μ + l ^ 2 * W / 2) ^ N := by gcongr
              _ = Real.exp (-(N * t ^ 2 / (2 * W))) := by
                rw [← Real.exp_nat_mul, ← Real.exp_add, hl]
                congr 1
                field_simp
                ring
          have hthrpos : ∀ B : ℝ, 0 ≤ (1 + pExp N / (2 - pExp N)) *
              ((2 : ℝ) ^ (1 / 2 + 1 / pExp N) / (N : ℝ) ^ (1 - 1 / pExp N)) *
              Real.sqrt ((d + 1 : ℝ) + (d + 1 : ℝ) * Real.log (N / (d + 1 : ℝ)) + Real.log (4 / α₁)) := by
            intro B
            obtain ⟨h1, h2, -⟩ := hpE N hN
            have : 0 < 2 - pExp N := by linarith
            have : 0 < (N : ℝ) := by have : (2:ℝ) ≤ N := by exact_mod_cast hN
                                     linarith
            positivity
          have hthr : ∀ B : ℝ, lcxThreshold d N α₁ B = (1 + B) * ((1 + pExp N / (2 - pExp N)) *
              ((2 : ℝ) ^ (1 / 2 + 1 / pExp N) / (N : ℝ) ^ (1 - 1 / pExp N)) *
              Real.sqrt ((d + 1 : ℝ) + (d + 1 : ℝ) * Real.log (N / (d + 1 : ℝ)) + Real.log (4 / α₁))) := by
            intro B; unfold lcxThreshold; ring
          -- Part 3
          have part3 : ∀ B : ℝ, ((secondMoment F : ℝ≥0∞) : EReal) ≤ (B : EReal) →
              dataLaw F {ω | ¬ (lcxStat F₀ (sample ω N) ≤ ((lcxThreshold d N α₁ B : ℝ) : EReal))} ≤
                ENNReal.ofReal α₁ := by
            clear hQbar Qbar hexp
            intro B hB
            have hPprob : IsProbabilityMeasure (dataLaw F) := by unfold dataLaw; infer_instance
            set μ : Measure ↥Ξ := (F : Measure ↥Ξ) with hμ
            have hN2 : (2:ℝ) ≤ N := by exact_mod_cast hN
            have hNpos : (0:ℝ) < N := by linarith
            have hsm_ne : secondMoment F ≠ ⊤ := by
              intro h; rw [h] at hB; simp at hB
            have hsmB : (secondMoment F).toReal ≤ B := by
              rw [← EReal.coe_ennreal_toReal hsm_ne] at hB; exact_mod_cast hB
            have hB0 : 0 ≤ B := le_trans ENNReal.toReal_nonneg hsmB
            have hcontv : Continuous (fun x : ↥Ξ => (x : Pt d)) := continuous_subtype_val
            have hnsq_meas : AEStronglyMeasurable (fun x : ↥Ξ => ‖(x : Pt d)‖ ^ 2) μ :=
              (hcontv.norm.pow 2).aestronglyMeasurable
            have hI : Integrable (fun x : ↥Ξ => ‖(x : Pt d)‖ ^ 2) μ :=
              ⟨hnsq_meas, (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => by positivity)).2
                (lt_top_iff_ne_top.2 hsm_ne)⟩
            have hIeq : ∫ x, ‖(x : Pt d)‖ ^ 2 ∂μ = (secondMoment F).toReal := by
              rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => by positivity) hnsq_meas]; rfl
            set m : ↥Ξ → ℝ := fun x => Real.sqrt (1 + ‖(x : Pt d)‖ ^ 2) with hm
            have hm_cont : Continuous m := (continuous_const.add (hcontv.norm.pow 2)).sqrt
            have hm2 : ∀ x, m x ^ 2 = 1 + ‖(x : Pt d)‖ ^ 2 := fun x => Real.sq_sqrt (by positivity)
            have hm0 : ∀ x, 0 ≤ m x := fun x => Real.sqrt_nonneg _
            have hm1 : ∀ x, 1 ≤ m x := fun x => 
              Real.one_le_sqrt.2 (le_add_of_nonneg_right (sq_nonneg _))
            have hmfun : (fun x => m x ^ 2) = fun x : ↥Ξ => 1 + ‖(x : Pt d)‖ ^ 2 := funext fun x => hm2 x
            have hmI2 : Integrable (fun x => m x ^ 2) μ := by
              rw [hmfun]; exact (integrable_const 1).add hI
            have hmI : Integrable m μ := hmI2.mono' hm_cont.aestronglyMeasurable
              (ae_of_all _ fun x => by
                rw [Real.norm_eq_abs, abs_of_nonneg (hm0 x)]; exact le_self_pow₀ (hm1 x) two_ne_zero)
            have hmint2 : ∫ x, m x ^ 2 ∂μ ≤ 1 + B := by
              rw [hmfun, integral_add (integrable_const 1) hI, hIeq]; simp; linarith
            have hmint : ∫ x, m x ∂μ ≤ 1 + B :=
              le_trans (integral_mono hmI hmI2 fun x => le_self_pow₀ (hm1 x) two_ne_zero) hmint2
            -- constants
            set n : ℝ := (d : ℝ) + 1 with hn
            have hn1 : 1 ≤ n := by have : (0:ℝ) ≤ d := Nat.cast_nonneg d
                                   linarith
            have hnN : n ≤ N := by
              have := (Nat.cast_le (α := ℝ)).2 hdN; push_cast at this; linarith
            set ε := Real.sqrt n / N with hε
            have hε0 : 0 ≤ ε := by positivity
            have hε2 : ε ^ 2 = n / N ^ 2 := by rw [hε, div_pow, Real.sq_sqrt (by linarith)]
            set W := 1 + B with hW
            have hW1 : 1 ≤ W := by linarith
            have hα0 := hα₁.1
            have hlogα : 0 ≤ Real.log (1 / α₁) := Real.log_nonneg (by rw [le_div_iff₀ hα0]; linarith [hα₁.2])
            have hK := hnum N n α₁ hN hn1 hnN hα₁.1 hα₁.2
            set Λ := n * Real.log (2 * N + 1) + Real.log (1 / α₁) with hΛ
            have hc0 : 0 ≤ Real.log (2 * N + 1) := Real.log_nonneg (by linarith)
            have hΛ0 : 0 ≤ Λ := by positivity
            set t := Real.sqrt (2 * W * Λ / N) with ht
            have ht0 : 0 ≤ t := Real.sqrt_nonneg _
            have ht2 : t ^ 2 = 2 * W * Λ / N := Real.sq_sqrt (by positivity)
            have htW : t ≤ W * Real.sqrt (2 * Λ / N) := by
              rw [ht, show 2 * W * Λ / N = W * (2 * Λ / N) by ring, Real.sqrt_mul (by linarith)]
              gcongr
              rw [Real.sqrt_le_left (by linarith)]; exact le_self_pow₀ hW1 two_ne_zero
            have hfinal : 2 * ε * W + t ≤ lcxThreshold d N α₁ B := by
              rw [hthr]
              have := mul_le_mul_of_nonneg_left hK (by linarith : (0:ℝ) ≤ W)
              calc 2 * ε * W + t ≤ 2 * ε * W + W * Real.sqrt (2 * Λ / N) := add_le_add le_rfl htW
                _ = W * (2 * Real.sqrt n / N + Real.sqrt (2 * Λ / N)) := by rw [hε]; ring
                _ ≤ _ := this
            clear hK hlogα hthr hthrpos hnum hpE htW
            -- grid
            let J := (Fin d → Fin (2 * N + 1)) × Fin (2 * N + 1)
            let ga : J → Pt d := fun j => WithLp.toLp 2 (fun i => (((j.1 i : ℕ) : ℝ) - N) / N)
            let gb : J → ℝ := fun j => (((j.2 : ℕ) : ℝ) - N) / N
            let g : J → ↥Ξ → ℝ := fun j x =>
              min (max (inner ℝ (ga j) (x : Pt d) - gb j - ε * m x) 0) (m x)
            have hg_cont : ∀ j, Continuous (g j) := fun j =>
              ((((continuous_const.inner hcontv).sub continuous_const).sub
                (continuous_const.mul hm_cont)).max continuous_const).min hm_cont
            have hg0 : ∀ j x, 0 ≤ g j x := fun j x => le_min (le_max_right _ _) (hm0 x)
            have hgm : ∀ j x, g j x ≤ m x := fun j x => min_le_right _ _
            have hgI : ∀ j, Integrable (g j) μ := fun j =>
              hmI.mono' (hg_cont j).aestronglyMeasurable (ae_of_all _ fun x => by
                rw [Real.norm_eq_abs, abs_of_nonneg (hg0 j x)]; exact hgm j x)
            have hgI2 : ∀ j, Integrable (fun x => g j x ^ 2) μ := fun j =>
              hmI2.mono' ((hg_cont j).pow 2).aestronglyMeasurable (ae_of_all _ fun x => by
                rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
                exact pow_le_pow_left₀ (hg0 j x) (hgm j x) 2)
            have hgW : ∀ j, ∫ x, g j x ^ 2 ∂μ ≤ W := fun j =>
              (integral_mono (hgI2 j) hmI2 fun x => pow_le_pow_left₀ (hg0 j x) (hgm j x) 2).trans hmint2
            let Bad : J → Set (ℕ → ↥Ξ) := fun j =>
              {ω | ∑ i ∈ Finset.range N, g j (ω i) ≤ N * (∫ x, g j x ∂μ - t)}
            have hBad : ∀ j, dataLaw F (Bad j) ≤ ENNReal.ofReal (Real.exp (-(N * t ^ 2 / (2 * W)))) :=
              fun j => hChern (g j) (hg_cont j).measurable (hg0 j) (hgI j) (hgI2 j) W t (by linarith) ht0
                (hgW j)
            clear hChern hgW hgI2
            have hexpeq : Real.exp (-(N * t ^ 2 / (2 * W))) = α₁ / ((2 * N + 1 : ℝ)) ^ (d + 1) := by
              rw [ht2]
              have h1 : -(N * (2 * W * Λ / N) / (2 * W)) = -Λ := by field_simp
              have e1 : Real.exp (n * Real.log (2 * N + 1)) = (2 * N + 1 : ℝ) ^ (d + 1) := by
                rw [show n = ((d + 1 : ℕ) : ℝ) by push_cast; ring, Real.exp_nat_mul,
                  Real.exp_log (by positivity)]
              have e2 : Real.exp (Real.log (1 / α₁)) = 1 / α₁ := Real.exp_log (by positivity)
              rw [h1, hΛ, neg_add, Real.exp_add, Real.exp_neg, Real.exp_neg, e1, e2]
              field_simp
            have hcard : Fintype.card J = (2 * N + 1) ^ (d + 1) := by
              simp only [J, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, pow_succ]
            have hunion : dataLaw F (⋃ j, Bad j) ≤ ENNReal.ofReal α₁ := by
              calc _ ≤ ∑ j, dataLaw F (Bad j) := measure_iUnion_fintype_le _ _
                _ ≤ ∑ j : J, ENNReal.ofReal (α₁ / ((2 * N + 1 : ℝ)) ^ (d + 1)) :=
                  Finset.sum_le_sum fun j _ => (hBad j).trans_eq (by rw [hexpeq])
                _ = ENNReal.ofReal α₁ := by
                  rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
                    ← ENNReal.ofReal_mul (by positivity)]
                  congr 1; push_cast; field_simp
            refine le_trans (measure_mono ?_) hunion
            clear hBad hexpeq hcard hunion hΛ0 hc0 ht2 hmint2 hmI2 hmfun hsm_ne hsmB hI hIeq hnsq_meas hB
            intro ω hω
            by_contra hcon
            simp only [Set.mem_iUnion, not_exists, Bad, Set.mem_ofPred_eq, not_le] at hcon
            apply hω
            unfold lcxStat
            refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_
            have hgrid : ∀ r : ℝ, |r| ≤ 1 → ∃ k : Fin (2 * N + 1),
                (r - (((k : ℕ) : ℝ) - N) / N) ^ 2 ≤ 1 / (N : ℝ) ^ 2 := by
              intro r hr
              obtain ⟨hr1, hr2⟩ := abs_le.1 hr
              have h0 : 0 ≤ (r + 1) * N := by exact mul_nonneg (by linarith only [hr1]) hNpos.le
              have hf1 := Nat.floor_le h0
              have hf2 := Nat.lt_floor_add_one ((r + 1) * N)
              have hk : ⌊(r + 1) * (N : ℝ)⌋₊ < 2 * N + 1 := by
                have : (⌊(r + 1) * (N : ℝ)⌋₊ : ℝ) < ((2 * N + 1 : ℕ) : ℝ) := by
                  push_cast; have := mul_le_mul_of_nonneg_right hr2 hNpos.le; linarith only [this, hf1]
                exact_mod_cast this
              refine ⟨⟨_, hk⟩, ?_⟩
              have e : r - (((⌊(r + 1) * (N : ℝ)⌋₊ : ℕ) : ℝ) - N) / N =
                  ((r + 1) * N - ⌊(r + 1) * (N : ℝ)⌋₊) / N := by field_simp; ring
              show (r - (((⌊(r + 1) * (N : ℝ)⌋₊ : ℕ) : ℝ) - N) / N) ^ 2 ≤ _
              rw [e, div_pow]
              apply div_le_div_of_nonneg_right _ (by positivity)
              exact pow_le_one₀ (by linarith only [hf1]) (by linarith only [hf2])
            have hCS : ∀ (c : Pt d) (e ρ : ℝ) (x : ↥Ξ), 0 ≤ ρ → (∑ i, c i ^ 2) + e ^ 2 ≤ ρ ^ 2 →
                |inner ℝ c (x : Pt d) - e| ≤ ρ * m x := by
              intro c e ρ x hρ hce
              have hcn : ‖c‖ ^ 2 = ∑ i, c i ^ 2 := EuclideanSpace.real_norm_sq_eq c
              rw [← hcn, ← sq_abs e] at hce
              apply abs_le_of_sq_le_sq _ (mul_nonneg hρ (hm0 x))
              rw [mul_pow, hm2]
              have h1 : |inner ℝ c (x : Pt d) - e| ≤ ‖c‖ * ‖(x : Pt d)‖ + |e| :=
                (abs_sub _ _).trans (add_le_add (abs_real_inner_le_norm _ _) le_rfl)
              have h2 : (inner ℝ c (x : Pt d) - e) ^ 2 ≤ (‖c‖ * ‖(x : Pt d)‖ + |e|) ^ 2 := by
                rw [← sq_abs (inner ℝ c (x : Pt d) - e)]
                exact pow_le_pow_left₀ (abs_nonneg _) h1 2
              have h3 : 0 ≤ 1 + ‖(x : Pt d)‖ ^ 2 := by positivity
              have h4 := mul_le_mul_of_nonneg_right hce h3
              have h5 := sq_nonneg (‖c‖ - |e| * ‖(x : Pt d)‖)
              linarith only [h2, h4, h5]
            have hb0 : 0 ≤ |b| := abs_nonneg b
            have hsum_nonneg : ∀ i ∈ (Finset.univ : Finset (Fin d)), 0 ≤ |a i| := fun i _ => abs_nonneg _
            have hl1 : 0 ≤ l1norm a := Finset.sum_nonneg hsum_nonneg
            have hai : ∀ i, |a i| ≤ 1 := fun i => by
              have := Finset.single_le_sum hsum_nonneg (Finset.mem_univ i)
              have h2 : l1norm a = ∑ j, |a j| := rfl
              linarith only [this, h2, hab, hb0]
            have hbi : |b| ≤ 1 := by linarith only [hab, hl1]
            choose ka hka using fun i => hgrid (a i) (hai i)
            obtain ⟨kb, hkb⟩ := hgrid b hbi
            let j : J := (ka, kb)
            have hab2 : (∑ i, a i ^ 2) + b ^ 2 ≤ 1 ^ 2 := by
              have h1 : ∑ i, a i ^ 2 ≤ ∑ i, |a i| := Finset.sum_le_sum fun i _ => by
                have := hai i
                rw [← sq_abs]; exact pow_le_of_le_one (abs_nonneg _) this two_ne_zero
              have h2 : b ^ 2 ≤ |b| := by rw [← sq_abs]; exact pow_le_of_le_one (abs_nonneg _) hbi two_ne_zero
              have h3 : l1norm a = ∑ j, |a j| := rfl
              linarith only [h1, h2, h3, hab]
            have hdiff : (∑ i, (a - ga j) i ^ 2) + (b - gb j) ^ 2 ≤ ε ^ 2 := by
              have h1 : ∑ i, (a - ga j) i ^ 2 ≤ ∑ i : Fin d, 1 / (N : ℝ) ^ 2 :=
                Finset.sum_le_sum fun i _ => hka i
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
              have h2 : (b - gb j) ^ 2 ≤ 1 / (N : ℝ) ^ 2 := hkb
              rw [hε2, hn, add_div]
              calc _ ≤ _ := add_le_add h1 h2
                _ = _ := by ring
            have hh1 : ∀ x : ↥Ξ, hinge a b (x : Pt d) ≤ m x := fun x => by
              have h1 := (abs_le.1 (hCS a b 1 x zero_le_one hab2)).2
              exact max_le (by linarith only [h1]) (hm0 x)
            have hh0 : ∀ x : ↥Ξ, 0 ≤ hinge a b (x : Pt d) := fun x => le_max_right _ _
            have hd : ∀ x : ↥Ξ, |(inner ℝ a (x : Pt d) - b) - (inner ℝ (ga j) (x : Pt d) - gb j)| ≤ ε * m x := by
              intro x
              have := hCS (a - ga j) (b - gb j) ε x hε0 hdiff
              rw [inner_sub_left] at this
              rwa [show (inner ℝ a (x : Pt d) - b) - (inner ℝ (ga j) (x : Pt d) - gb j) =
                inner ℝ a (x : Pt d) - inner ℝ (ga j) (x : Pt d) - (b - gb j) by ring]
            have hgle : ∀ x : ↥Ξ, g j x ≤ hinge a b (x : Pt d) := fun x => by
              have h1 := (abs_le.1 (hd x)).1
              refine (min_le_left _ _).trans ?_
              exact max_le_max (by linarith only [h1]) le_rfl
            have hhle : ∀ x : ↥Ξ, hinge a b (x : Pt d) ≤ g j x + 2 * ε * m x := fun x => by
              have h1 := (abs_le.1 (hd x)).2
              have h2 := hh1 x
              have h3 := mul_nonneg hε0 (hm0 x)
              rw [← sub_le_iff_le_add]
              refine le_min ?_ (by linarith only [h2, h3])
              rw [sub_le_iff_le_add]
              refine max_le ?_ ?_
              · linarith only [h1, le_max_left (inner ℝ (ga j) (x : Pt d) - gb j - ε * m x) 0]
              · linarith only [h3, le_max_right (inner ℝ (ga j) (x : Pt d) - gb j - ε * m x) 0]
            have hhcont : Continuous (fun x : ↥Ξ => hinge a b (x : Pt d)) :=
              ((continuous_const.inner hcontv).sub continuous_const).max continuous_const
            have hhI : Integrable (fun x : ↥Ξ => hinge a b (x : Pt d)) μ :=
              hmI.mono' hhcont.aestronglyMeasurable (ae_of_all _ fun x => by
                rw [Real.norm_eq_abs, abs_of_nonneg (hh0 x)]; exact hh1 x)
            have hmean : hingeMean F a b = ENNReal.ofReal (∫ x, hinge a b (x : Pt d) ∂μ) :=
              (ofReal_integral_eq_lintegral_ofReal hhI (ae_of_all _ hh0)).symm
            have hint0 : 0 ≤ ∫ x, hinge a b (x : Pt d) ∂μ := integral_nonneg hh0
            have hupper : ∫ x, hinge a b (x : Pt d) ∂μ ≤ ∫ x, g j x ∂μ + 2 * ε * W := by
              calc _ ≤ ∫ x, (g j x + 2 * ε * m x) ∂μ :=
                    integral_mono hhI ((hgI j).add (hmI.const_mul _)) hhle
                _ = ∫ x, g j x ∂μ + 2 * ε * ∫ x, m x ∂μ := by
                    rw [integral_add (hgI j) (hmI.const_mul _), integral_const_mul]
                _ ≤ _ := by
                    have := mul_le_mul_of_nonneg_left hmint (mul_nonneg zero_le_two hε0)
                    linarith only [this]
            have hemp : ∫ x, g j x ∂μ - t ≤
                1 / (N : ℝ) * ∑ i, hinge a b ((sample ω N i : ↥Ξ) : Pt d) := by
              have h1 := hcon j
              have h2 : ∑ i ∈ Finset.range N, g j (ω i) ≤
                  ∑ i, hinge a b ((sample ω N i : ↥Ξ) : Pt d) := by
                rw [Finset.sum_range]
                exact Finset.sum_le_sum fun i _ => hgle (ω i)
              rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hNpos]
              linarith only [h1, h2]
            have hF0 : ((hingeMean F₀ a b : ℝ≥0∞) : EReal) ≤
                ((∫ x, hinge a b (x : Pt d) ∂μ : ℝ) : EReal) := by
              calc ((hingeMean F₀ a b : ℝ≥0∞) : EReal) ≤ ((hingeMean F a b : ℝ≥0∞) : EReal) :=
                    EReal.coe_ennreal_le_coe_ennreal_iff.2 (hLCX a b hab)
                _ = _ := by rw [hmean, EReal.coe_ennreal_ofReal, max_eq_left hint0]
            refine (EReal.sub_le_sub hF0 le_rfl).trans ?_
            rw [← EReal.coe_sub]
            apply EReal.coe_le_coe_iff.2
            linarith only [hupper, hemp, hfinal]
          refine ⟨⟨(hpE N hN).1, (hpE N hN).2.1⟩, ?_, part3⟩
          -- Part 2
          have : IsProbabilityMeasure (dataLaw F) := by unfold dataLaw; infer_instance
          by_cases hsm : secondMoment F = ⊤
          · have hall : {ω : ℕ → ↥Ξ | ¬ (((secondMoment F : ℝ≥0∞) : EReal) ≤
                ((Qbar (sample ω N) : ℝ) : EReal))} = Set.univ := by
              ext ω; simp [hsm]
            rw [hall, measure_univ] at hQbar
            have : (1:ℝ) ≤ α₂ := by
              have := (ENNReal.one_le_ofReal).1 hQbar
              exact this
            calc _ ≤ (1 : ℝ≥0∞) := prob_le_one
              _ ≤ _ := by rw [ENNReal.one_le_ofReal]; linarith [hα₁.1]
          · set B0 := (secondMoment F).toReal
            have hB0 : ((secondMoment F : ℝ≥0∞) : EReal) = (B0 : EReal) :=
              (EReal.coe_ennreal_toReal hsm).symm
            have hsub : {ω : ℕ → ↥Ξ | ¬ (((secondMoment F : ℝ≥0∞) : EReal) ≤ ((Qbar (sample ω N) : ℝ) : EReal) ∧
                lcxStat F₀ (sample ω N) ≤ ((lcxThreshold d N α₁ (Qbar (sample ω N)) : ℝ) : EReal))} ⊆
                {ω | ¬ (((secondMoment F : ℝ≥0∞) : EReal) ≤ ((Qbar (sample ω N) : ℝ) : EReal))} ∪
                {ω | ¬ (lcxStat F₀ (sample ω N) ≤ ((lcxThreshold d N α₁ B0 : ℝ) : EReal))} := by
              intro ω hω
              by_contra hc
              simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hc hω
              refine hω ⟨hc.1, hc.2.trans ?_⟩
              rw [hB0] at hc
              have hq : B0 ≤ Qbar (sample ω N) := by exact_mod_cast hc.1
              rw [hthr, hthr]
              exact_mod_cast mul_le_mul_of_nonneg_right (by linarith) (hthrpos 0)
            calc _ ≤ _ := measure_mono hsub
              _ ≤ _ := measure_union_le _ _
              _ ≤ ENNReal.ofReal α₂ + ENNReal.ofReal α₁ := add_le_add hQbar (part3 B0 hB0.le)
              _ = _ := by rw [← ENNReal.ofReal_add hα₂ hα₁.1.le, add_comm]
