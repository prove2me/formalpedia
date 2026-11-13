-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P15.secondPrinciple_extendedMean
-- status  : ACCEPTED   (prove)
-- author  : @Yivy Yu
-- created : 2026-11-13T02:08:52.145488+00:00
-- url     : https://prove2.me/submissions/1451e237-bbe1-4c18-8804-c0b92ab8b1db

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P15_jarzynski_identity

open MeasureTheory Filter
open QAlgorithms.Papers.Independent.Intakethird100.P15
open QAlgorithms.Papers.Independent.Information100.P37 (transition)
open QAlgorithms.Papers.Independent.Next46.P01 (extendedExpectation)
open scoped ENNReal Topology

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type v} {Ω : Type w} [MeasurableSpace Ω]

private theorem workLaw_univ [Countable ι] [Nonempty ι]
    (b : HilbertBasis ι ℂ E) (U : E ≃ₗᵢ[ℂ] E)
    (energy : ι → ℝ) (beta : ℝ) (hbeta : 0 < beta) (hheat : HasFiniteHeatTraces energy) :
    workLaw b U energy beta Set.univ = 1 := by
  classical
  let weight := spectralGibbsWeight energy beta
  let born : ι → ι → ℝ := transition (fun g a => inner ℂ (b g) (U (b a)))
  have hsum := hheat beta hbeta
  have hZ : 0 < heatTrace energy beta := by
    let i : ι := Classical.choice ‹Nonempty ι›
    exact (Real.exp_pos _).trans_le (hsum.le_tsum i (fun j _ => (Real.exp_pos _).le))
  have hw (i : ι) : 0 ≤ weight i := div_nonneg (Real.exp_pos _).le hZ.le
  have hwsum : Summable weight := hsum.div_const _
  have hweight : (∑' i, weight i) = 1 := by
    change (∑' i, Real.exp (-beta * energy i) / heatTrace energy beta) = 1
    rw [tsum_div_const, ← heatTrace, div_self hZ.ne']
  have hcol (a : ι) : (∑' g, ENNReal.ofReal (born g a)) = 1 := by
    let v := U (b a)
    have hterm (g : ι) : (inner ℂ v (b g) * inner ℂ (b g) v).re = born g a := by
      change (inner ℂ v (b g) * inner ℂ (b g) v).re = Complex.normSq (inner ℂ (b g) v)
      rw [mul_comm, ← inner_conj_symm (𝕜 := ℂ) v (b g), Complex.mul_conj, Complex.ofReal_re]
    have hnorm : ‖v‖ = 1 := by
      rw [show ‖v‖ = ‖b a‖ from U.norm_map _, b.orthonormal.norm_eq_one a]
    have hre : (inner ℂ v v).re = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hnorm]
      simp
    have hs : HasSum (fun g => born g a) 1 := by
      simpa only [hterm, hre] using Complex.hasSum_re (b.hasSum_inner_mul_inner v v)
    have hborn (g : ι) : 0 ≤ born g a := Complex.normSq_nonneg _
    rw [← ENNReal.ofReal_tsum_of_nonneg hborn hs.summable,
      hs.tsum_eq, ENNReal.ofReal_one]
  calc
    _ = ∑' p : ι × ι, ENNReal.ofReal (weight p.1 * born p.2 p.1) := by
      unfold workLaw preparedWorkLaw
      rw [Measure.sum_apply _ MeasurableSet.univ]
      simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem (Set.mem_univ _),
        mul_one, weight, born]
    _ = ∑' a : ι, ENNReal.ofReal (weight a) := by
      rw [ENNReal.tsum_prod']
      refine tsum_congr fun a => ?_
      simp_rw [ENNReal.ofReal_mul (hw a), ENNReal.tsum_mul_left, hcol a, mul_one]
    _ = 1 := by rw [← ENNReal.ofReal_tsum_of_nonneg hw hwsum, hweight, ENNReal.ofReal_one]

private theorem extended_eq_integral {P : Measure ℝ} {f : ℝ → ℝ} (hf : Integrable f P) :
    extendedExpectation P f = ((∫ e, f e ∂P : ℝ) : EReal) := by
  have hnorm := (hasFiniteIntegral_iff_norm f).mp hf.hasFiniteIntegral
  have hp : (∫⁻ e, ENNReal.ofReal (f e) ∂P) ≠ ∞ := ne_of_lt <| lt_of_le_of_lt
    (lintegral_mono fun e => ENNReal.ofReal_le_ofReal (by rw [Real.norm_eq_abs]; exact le_abs_self _))
    hnorm
  have hn : (∫⁻ e, ENNReal.ofReal (-f e) ∂P) ≠ ∞ := ne_of_lt <| lt_of_le_of_lt
    (lintegral_mono fun e => ENNReal.ofReal_le_ofReal (by rw [Real.norm_eq_abs]; exact neg_le_abs _))
    hnorm
  rw [extendedExpectation, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf,
    EReal.coe_sub, EReal.coe_ennreal_toReal hp, EReal.coe_ennreal_toReal hn]

theorem solution [Countable ι] [Nonempty ι]
    (b : HilbertBasis ι ℂ E) (d : CyclicDrive (Ω := Ω) b)
    (energy : ι → ℝ) (beta : ℝ) (hbeta : 0 < beta)
    (henergy : IsInitialEnergyBasis b d energy) (hheat : HasFiniteHeatTraces energy) :
    let P := workLaw b d.evolution energy beta
    Integrable (fun e : ℝ => max (-e) 0) P ∧
    (∫⁻ e, ENNReal.ofReal (max (-e) 0) ∂P) < ∞ ∧
    (0 : EReal) = ((-(1 / beta) * Real.log (∫ e, Real.exp (-beta * e) ∂P) : ℝ) : EReal) ∧
    ((-(1 / beta) * Real.log (∫ e, Real.exp (-beta * e) ∂P) : ℝ) : EReal) ≤
      ((-(1 / beta) : ℝ) : EReal) * extendedExpectation P (fun e => Real.log (Real.exp (-beta * e))) ∧
    ((-(1 / beta) : ℝ) : EReal) * extendedExpectation P (fun e => Real.log (Real.exp (-beta * e))) =
      extendedExpectation P (fun e => e) ∧
    (Integrable (fun e : ℝ => e) P →
      extendedExpectation P (fun e => e) = (((∫ e : ℝ, e ∂P) : ℝ) : EReal)) := by
  let P := workLaw b d.evolution energy beta
  letI : IsProbabilityMeasure P := ⟨workLaw_univ b d.evolution energy beta hbeta hheat⟩
  have hj := jarzynski_identity b d energy beta hbeta henergy hheat
  have hexp : Integrable (fun e : ℝ => Real.exp (-beta * e)) P := hj.1
  have hmoment : (∫ e, Real.exp (-beta * e) ∂P) = 1 := hj.2.1
  have hneg_nn : 0 ≤ᵐ[P] (fun e : ℝ => max (-e) 0) :=
    Eventually.of_forall fun _ => le_max_right _ _
  have hneg : Integrable (fun e : ℝ => max (-e) 0) P := by
    refine (hexp.const_mul beta⁻¹).mono_nonneg
      (show Continuous (fun e : ℝ => max (-e) 0) by fun_prop).aestronglyMeasurable hneg_nn ?_
    apply Eventually.of_forall
    intro e
    change max (-e) 0 ≤ beta⁻¹ * Real.exp (-beta * e)
    apply max_le
    · rw [mul_comm, ← div_eq_mul_inv, le_div_iff₀ hbeta]
      calc
        -e * beta ≤ -beta * e + 1 := by linarith only [mul_comm e beta]
        _ ≤ _ := Real.add_one_le_exp _
    · positivity
  have hnegInf := (hasFiniteIntegral_iff_ofReal hneg_nn).mp hneg.hasFiniteIntegral
  have hnfinite : (∫⁻ e : ℝ, ENNReal.ofReal (-e) ∂P) ≠ ∞ := by simpa using hnegInf.ne
  have hscaling :
      ((-(1 / beta) : ℝ) : EReal) * extendedExpectation P (fun e : ℝ => -beta * e) =
        extendedExpectation P (fun e : ℝ => e) ∧
      0 ≤ extendedExpectation P (fun e : ℝ => e) := by
    by_cases hp : (∫⁻ e : ℝ, ENNReal.ofReal e ∂P) = ∞
    · have hpos_top : extendedExpectation P (fun e : ℝ => e) = ⊤ := by
        rw [extendedExpectation, hp, EReal.coe_ennreal_top]
        apply EReal.top_sub
        simpa only [ne_eq, EReal.coe_ennreal_eq_top_iff] using hnfinite
      have hscaled_top : (∫⁻ e : ℝ, ENNReal.ofReal (-(-beta * e)) ∂P) = ∞ := by
        have hflip (e : ℝ) : -(-beta * e) = beta * e := by ring
        simp_rw [hflip, ENNReal.ofReal_mul hbeta.le]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hp, ENNReal.mul_top]
        exact (ENNReal.ofReal_pos.mpr hbeta).ne'
      have hscaled_bot : extendedExpectation P (fun e : ℝ => -beta * e) = ⊥ := by
        rw [extendedExpectation, hscaled_top, EReal.coe_ennreal_top, EReal.sub_top]
      rw [hpos_top, hscaled_bot, EReal.coe_mul_bot_of_neg (neg_lt_zero.mpr (one_div_pos.mpr hbeta))]
      exact ⟨rfl, le_top⟩
    · have hpos : Integrable (fun e : ℝ => max e 0) P := by
        refine (lintegral_ofReal_ne_top_iff_integrable
          (show Continuous (fun e : ℝ => max e 0) by fun_prop).aestronglyMeasurable
          (Eventually.of_forall fun e => le_max_right e 0)).mp ?_
        simpa using hp
      have hid : Integrable (fun e : ℝ => e) P := by
        refine (hpos.sub hneg).congr (Eventually.of_forall fun e => ?_)
        change max e 0 - max (-e) 0 = e
        rcases le_total 0 e with he | he
        · simp [max_eq_left he, max_eq_right (neg_nonpos.mpr he)]
        · simp [max_eq_right he, max_eq_left (neg_nonneg.mpr he)]
      have hconst : Integrable (fun _ : ℝ => (1 : ℝ)) P := integrable_const _
      have hmul := hid.const_mul beta
      have hlin : (∫ e : ℝ, (1 - beta * e) ∂P) ≤ ∫ e, Real.exp (-beta * e) ∂P :=
        integral_mono (hconst.sub hmul) hexp (fun e => by
          simpa [neg_mul, sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-beta * e))
      rw [integral_sub hconst hmul, integral_const, integral_const_mul, hmoment] at hlin
      have hnonneg : 0 ≤ ∫ e : ℝ, e ∂P := by
        have hbound : 1 - beta * (∫ e : ℝ, e ∂P) ≤ 1 := by simpa using hlin
        exact (mul_nonneg_iff_of_pos_left hbeta).mp (by linarith only [hbound])
      refine ⟨?_, ?_⟩
      · rw [extended_eq_integral (hid.const_mul (-beta)), extended_eq_integral hid,
          integral_const_mul, ← EReal.coe_mul]
        congr 1
        field_simp
      · rw [extended_eq_integral hid]
        exact EReal.coe_nonneg.mpr hnonneg
  refine ⟨hneg, hnegInf, ?_, ?_, ?_, fun hi => extended_eq_integral hi⟩
  · change (0 : EReal) = ((-(1 / beta) * Real.log (∫ e, Real.exp (-beta * e) ∂P) : ℝ) : EReal)
    rw [hmoment, Real.log_one, mul_zero, EReal.coe_zero]
  · change ((-(1 / beta) * Real.log (∫ e, Real.exp (-beta * e) ∂P) : ℝ) : EReal) ≤
      ((-(1 / beta) : ℝ) : EReal) * extendedExpectation P (fun e => Real.log (Real.exp (-beta * e)))
    rw [hmoment, Real.log_one, mul_zero, EReal.coe_zero]
    simpa only [Real.log_exp, hscaling.1] using hscaling.2
  · simpa only [Real.log_exp] using hscaling.1
