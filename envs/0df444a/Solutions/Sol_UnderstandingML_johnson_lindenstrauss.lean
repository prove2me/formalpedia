-- Prove2me | solution 1 for UnderstandingML.johnson_lindenstrauss
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T14:34:35.44421+00:00
-- url     : https://prove2.me/submissions/0ab0dccf-6f7f-4900-8a95-7c9741fd63fd

import Definitions.Def_UnderstandingML_DimReduction
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

open MeasureTheory ProbabilityTheory

namespace UnderstandingML.JLAux

/-! ### Two elementary inequalities -/

lemma upper_ineq (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 3 / 4) : 1 + ε ≤ Real.exp (ε - ε ^ 2 / 3) := by
  have hy : 0 ≤ ε - ε ^ 2 / 3 := by nlinarith
  have := Real.sum_le_exp_of_nonneg hy 4
  simp [Finset.sum_range_succ, Nat.factorial] at this
  refine le_trans ?_ this
  nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1), mul_nonneg (mul_nonneg h0 h0) (sub_nonneg.mpr h1),
    mul_nonneg (mul_nonneg h0 h0) (mul_nonneg h0 (sub_nonneg.mpr h1)), pow_nonneg h0 3,
    pow_nonneg h0 4, mul_nonneg (pow_nonneg h0 4) (sub_nonneg.mpr h1), pow_nonneg h0 5,
    pow_nonneg h0 6]

lemma lower_ineq (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 3 / 4) :
    1 - ε ≤ Real.exp (-ε - ε ^ 2 / 3) := by
  have hy : 0 ≤ ε + ε ^ 2 / 3 := by nlinarith
  have hy2 : ε + ε ^ 2 / 3 < 2 := by nlinarith
  have hexp := Real.exp_le_two_add_div_two_sub hy hy2
  have hpos := Real.exp_pos (ε + ε ^ 2 / 3)
  rw [show -ε - ε ^ 2 / 3 = -(ε + ε ^ 2 / 3) by ring, Real.exp_neg]
  rw [le_inv_comm₀ (by linarith) hpos]
  refine le_trans hexp ?_
  rw [div_le_iff₀ (by linarith)]
  rw [inv_mul_eq_div, le_div_iff₀ (by linarith)]
  nlinarith

lemma sqNorm_nonneg {d : ℕ} (x : Fin d → ℝ) : 0 ≤ sqNorm x :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-! ### The Gaussian integral `E exp(t Z²)` -/

lemma lintegral_exp_sq_gaussianReal (c : NNReal) (hc : 0 < c) (t : ℝ) (ht : 2 * c * t < 1) :
    ∫⁻ z, ENNReal.ofReal (Real.exp (t * z ^ 2)) ∂(gaussianReal 0 c) =
      ENNReal.ofReal (1 / Real.sqrt (1 - 2 * c * t)) := by
  have hcR : (0 : ℝ) < c := hc
  set b : ℝ := 1 / (2 * c) - t with hbdef
  have hb : 0 < b := by
    rw [hbdef, sub_pos, lt_div_iff₀ (by positivity)]; linarith
  rw [gaussianReal_of_var_ne_zero 0 hc.ne',
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF 0 c) (by fun_prop)]
  have hfun : ∀ z : ℝ, (gaussianPDF 0 c * fun z => ENNReal.ofReal (Real.exp (t * z ^ 2))) z =
      ENNReal.ofReal ((Real.sqrt (2 * Real.pi * c))⁻¹ * Real.exp (-b * z ^ 2)) := by
    intro z
    simp only [Pi.mul_apply, gaussianPDF]
    rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 c z), gaussianPDFReal, mul_assoc,
      ← Real.exp_add]
    congr 3
    rw [hbdef]; field_simp; ring
  simp_rw [hfun]
  rw [← ofReal_integral_eq_lintegral_ofReal ((integrable_exp_neg_mul_sq hb).const_mul _)
    (ae_of_all _ (fun z => by positivity))]
  congr 1
  rw [integral_const_mul, integral_gaussian]
  have h1 : 0 < 1 - 2 * c * t := by linarith
  have h2 : Real.pi / b = 2 * Real.pi * c / (1 - 2 * c * t) := by
    rw [hbdef]; field_simp
  rw [h2, Real.sqrt_div (by positivity)]
  have h3 : 0 < Real.sqrt (2 * Real.pi * c) := Real.sqrt_pos.mpr (by positivity)
  field_simp

/-! ### The law of one row functional -/

lemma row_law {d : ℕ} (v : NNReal) (x : Fin d → ℝ) :
    (Measure.pi (fun _ : Fin d => gaussianReal 0 v)).map (fun w => ∑ j, w j * x j) =
      gaussianReal 0 (v * (sqNorm x).toNNReal) := by
  apply Measure.ext_of_charFun
  funext u
  have hmeas : Measurable (fun w : Fin d → ℝ => ∑ j, w j * x j) := by fun_prop
  rw [charFun_apply_real, charFun_gaussianReal, integral_map hmeas.aemeasurable (by fun_prop)]
  have hprod : ∀ w : Fin d → ℝ, Complex.exp (↑u * ↑(∑ j, w j * x j) * Complex.I) =
      ∏ j, Complex.exp (↑(u * x j) * ↑(w j) * Complex.I) := by
    intro w
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  simp_rw [hprod]
  rw [integral_fintype_prod_eq_prod (fun j (w : ℝ) => Complex.exp (↑(u * x j) * ↑w * Complex.I))]
  simp_rw [← charFun_apply_real, charFun_gaussianReal]
  rw [← Complex.exp_sum]
  congr 1
  rw [NNReal.coe_mul, Real.coe_toNNReal _ (sqNorm_nonneg x)]
  simp only [sqNorm]
  push_cast
  simp only [mul_zero, zero_mul, zero_sub, Finset.sum_neg_distrib, Finset.mul_sum,
    Finset.sum_mul, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-! ### The exponential moment of `‖Wx‖²` -/

lemma lintegral_exp_sqNorm {n d : ℕ} (v : NNReal) (x : Fin d → ℝ) (t : ℝ)
    (hc : 0 < v * sqNorm x) (ht : 2 * (v * sqNorm x) * t < 1) :
    ∫⁻ W, ENNReal.ofReal (Real.exp (t * sqNorm ((Matrix.of W).mulVec x))) ∂gaussianMatrixLaw n d v =
      ENNReal.ofReal ((1 / Real.sqrt (1 - 2 * (v * sqNorm x) * t)) ^ n) := by
  have hcR : ((v * (sqNorm x).toNNReal : NNReal) : ℝ) =
      v * sqNorm x := by rw [NNReal.coe_mul, Real.coe_toNNReal _ (sqNorm_nonneg x)]
  let F : (Fin d → ℝ) → ENNReal := fun w => ENNReal.ofReal (Real.exp (t * (∑ j, w j * x j) ^ 2))
  have hFmeas : Measurable F := by
    simp only [F]; fun_prop
  have hfac : ∀ W : Fin n → Fin d → ℝ,
      ENNReal.ofReal (Real.exp (t * sqNorm ((Matrix.of W).mulVec x))) = ∏ i, F (W i) := by
    intro W
    simp only [F, sqNorm, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum,
      Real.exp_sum]
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le)]
  simp_rw [hfac]
  unfold gaussianMatrixLaw
  have hind : iIndepFun (fun (i : Fin n) (W : Fin n → Fin d → ℝ) => F (W i))
      (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 v) :=
    iIndepFun_pi (fun _ => hFmeas.aemeasurable)
  have key := lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hind
    (fun i => hFmeas.comp (measurable_pi_apply i))
  rw [key]
  have hone : ∀ i : Fin n, ∫⁻ W, F (W i) ∂(Measure.pi fun _ : Fin n =>
      Measure.pi fun _ : Fin d => gaussianReal 0 v) =
      ENNReal.ofReal (1 / Real.sqrt (1 - 2 * (v * sqNorm x) * t)) := by
    intro i
    rw [(measurePreserving_eval (fun _ : Fin n =>
      Measure.pi fun _ : Fin d => gaussianReal 0 v) i).lintegral_comp hFmeas]
    have hY : Measurable (fun w : Fin d → ℝ => ∑ j, w j * x j) := by fun_prop
    have hG : Measurable (fun y : ℝ => ENNReal.ofReal (Real.exp (t * y ^ 2))) := by fun_prop
    show ∫⁻ w, (fun y : ℝ => ENNReal.ofReal (Real.exp (t * y ^ 2))) (∑ j, w j * x j)
      ∂(Measure.pi fun _ : Fin d => gaussianReal 0 v) = _
    rw [← lintegral_map hG hY, row_law v x]
    rw [← hcR]
    exact lintegral_exp_sq_gaussianReal _ (by rw [← NNReal.coe_pos, hcR]; exact hc)
      t (by rw [hcR]; exact ht)
  rw [Finset.prod_congr rfl (fun i _ => hone i), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← ENNReal.ofReal_pow (by positivity)]


lemma sqNorm_pos {d : ℕ} {v : Fin d → ℝ} (hv : v ≠ 0) : 0 < sqNorm v := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  unfold sqNorm
  exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (f := fun j => v j ^ 2)
    (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i))

/-- Markov's inequality for `exp (t g)`, in `ℝ≥0∞`, valid for any set. -/
lemma markov_exp {α : Type*} [MeasurableSpace α] (μ : Measure α) (g : α → ℝ) (hg : Measurable g)
    (t a : ℝ) (ht : 0 ≤ t) :
    μ {w | a ≤ g w} ≤
      ENNReal.ofReal (Real.exp (-(t * a))) * ∫⁻ w, ENNReal.ofReal (Real.exp (t * g w)) ∂μ := by
  have hsub : {w | a ≤ g w} ⊆
      {w | ENNReal.ofReal (Real.exp (t * a)) ≤ ENNReal.ofReal (Real.exp (t * g w))} := by
    intro w hw
    simp only [Set.mem_ofPred_eq] at hw ⊢
    apply ENNReal.ofReal_le_ofReal
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hw ht)
  have hmeas : AEMeasurable (fun w => ENNReal.ofReal (Real.exp (t * g w))) μ := by
    fun_prop
  have key := mul_meas_ge_le_lintegral₀ hmeas (ENNReal.ofReal (Real.exp (t * a)))
  calc μ {w | a ≤ g w}
      ≤ μ {w | ENNReal.ofReal (Real.exp (t * a)) ≤ ENNReal.ofReal (Real.exp (t * g w))} :=
        measure_mono hsub
    _ = ENNReal.ofReal (Real.exp (-(t * a))) * (ENNReal.ofReal (Real.exp (t * a)) *
          μ {w | ENNReal.ofReal (Real.exp (t * a)) ≤ ENNReal.ofReal (Real.exp (t * g w))}) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
          neg_add_cancel, Real.exp_zero, ENNReal.ofReal_one, one_mul]
    _ ≤ _ := by gcongr

/-! ### The single-vector tail bound (Lemma 23.3 with variance `1/n`) -/

lemma single_tail {n d : ℕ} (hn : 0 < n) (x : Fin d → ℝ) (hx : x ≠ 0) (ε : ℝ) (hε0 : 0 < ε)
    (hε : ε ≤ 3 / 4) :
    gaussianMatrixLaw n d (n : NNReal)⁻¹
      {W | ε ≤ |sqNorm ((Matrix.of W).mulVec x) / sqNorm x - 1|} ≤
      ENNReal.ofReal (2 * Real.exp (-(ε ^ 2 * n / 6))) := by
  set μ := gaussianMatrixLaw n d (n : NNReal)⁻¹ with hμ
  set q := sqNorm x with hq
  set S : (Fin n → Fin d → ℝ) → ℝ := fun W => sqNorm ((Matrix.of W).mulVec x) with hS
  have hqpos : 0 < q := sqNorm_pos hx
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcq : (((n : NNReal)⁻¹ : NNReal) : ℝ) * q = q / n := by
    simp [div_eq_inv_mul]
  have hc : 0 < (((n : NNReal)⁻¹ : NNReal) : ℝ) * q := by rw [hcq]; positivity
  have hSmeas : Measurable S := by
    simp only [hS, sqNorm, Matrix.mulVec, dotProduct, Matrix.of_apply]
    fun_prop
  have hε1 : ε < 1 := by linarith
  -- the event splits into an upper and a lower tail
  have hsub : {W | ε ≤ |S W / q - 1|} ⊆
      {W | (1 + ε) * q ≤ S W} ∪ {W | -((1 - ε) * q) ≤ -S W} := by
    intro W hW
    simp only [Set.mem_ofPred_eq] at hW
    rcases le_abs'.mp hW with h | h
    · right
      simp only [Set.mem_ofPred_eq, neg_le_neg_iff]
      have : S W / q ≤ 1 - ε := by linarith
      rwa [div_le_iff₀ hqpos] at this
    · left
      simp only [Set.mem_ofPred_eq]
      have : 1 + ε ≤ S W / q := by linarith
      rwa [le_div_iff₀ hqpos] at this
  -- upper tail
  have hup : μ {W | (1 + ε) * q ≤ S W} ≤ ENNReal.ofReal (Real.exp (-(ε ^ 2 * n / 6))) := by
    set t := ε / (2 * (q / n) * (1 + ε)) with ht
    have ht0 : 0 ≤ t := by positivity
    have h2ct : 2 * ((((n : NNReal)⁻¹ : NNReal) : ℝ) * q) * t = ε / (1 + ε) := by
      rw [hcq, ht]; field_simp
    have h2ct1 : 2 * ((((n : NNReal)⁻¹ : NNReal) : ℝ) * q) * t < 1 := by
      rw [h2ct, div_lt_one (by linarith)]; linarith
    refine le_trans (markov_exp μ S hSmeas t _ ht0) ?_
    rw [lintegral_exp_sqNorm _ x t hc h2ct1, h2ct, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    have e1 : t * ((1 + ε) * q) = ε * n / 2 := by rw [ht]; field_simp
    have e2 : 1 / Real.sqrt (1 - ε / (1 + ε)) = Real.sqrt (1 + ε) := by
      rw [show 1 - ε / (1 + ε) = 1 / (1 + ε) by field_simp; ring, Real.sqrt_div' _ (by linarith),
        Real.sqrt_one, one_div_one_div]
    rw [e1, e2]
    have hbase : Real.exp (-(ε / 2)) * Real.sqrt (1 + ε) ≤ Real.exp (-(ε ^ 2 / 6)) := by
      have h1 : Real.sqrt (1 + ε) ≤ Real.sqrt (Real.exp (ε - ε ^ 2 / 3)) :=
        Real.sqrt_le_sqrt (upper_ineq ε hε0.le hε)
      have h2 : Real.sqrt (Real.exp (ε - ε ^ 2 / 3)) = Real.exp ((ε - ε ^ 2 / 3) / 2) := by
        rw [← Real.sqrt_sq (Real.exp_pos ((ε - ε ^ 2 / 3) / 2)).le, ← Real.exp_nat_mul]
        congr 2; push_cast; ring
      rw [h2] at h1
      calc Real.exp (-(ε / 2)) * Real.sqrt (1 + ε)
          ≤ Real.exp (-(ε / 2)) * Real.exp ((ε - ε ^ 2 / 3) / 2) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = Real.exp (-(ε ^ 2 / 6)) := by rw [← Real.exp_add]; congr 1; ring
    calc Real.exp (-(ε * n / 2)) * Real.sqrt (1 + ε) ^ n
        = (Real.exp (-(ε / 2)) * Real.sqrt (1 + ε)) ^ n := by
          rw [mul_pow, ← Real.exp_nat_mul]; congr 2; ring
      _ ≤ (Real.exp (-(ε ^ 2 / 6))) ^ n :=
          pow_le_pow_left₀ (by positivity) hbase n
      _ = Real.exp (-(ε ^ 2 * n / 6)) := by rw [← Real.exp_nat_mul]; congr 1; ring
  -- lower tail
  have hlow : μ {W | -((1 - ε) * q) ≤ -S W} ≤ ENNReal.ofReal (Real.exp (-(ε ^ 2 * n / 6))) := by
    set t := ε / (2 * (q / n) * (1 - ε)) with ht
    have h1ε : 0 < 1 - ε := by linarith
    have ht0 : 0 ≤ t := by positivity
    have h2ct : 2 * ((((n : NNReal)⁻¹ : NNReal) : ℝ) * q) * (-t) = -(ε / (1 - ε)) := by
      rw [hcq, ht]; field_simp
    have h2ct1 : 2 * ((((n : NNReal)⁻¹ : NNReal) : ℝ) * q) * (-t) < 1 := by
      rw [h2ct]; have : 0 ≤ ε / (1 - ε) := by positivity
      linarith
    refine le_trans (markov_exp μ (fun W => -S W) hSmeas.neg t _ ht0) ?_
    have hrw : ∀ W, t * -S W = (-t) * S W := fun W => by ring
    simp only [hrw]
    rw [lintegral_exp_sqNorm _ x (-t) hc h2ct1, h2ct, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    have e1 : -(t * -((1 - ε) * q)) = ε * n / 2 := by rw [ht]; field_simp
    have e2 : 1 / Real.sqrt (1 - -(ε / (1 - ε))) = Real.sqrt (1 - ε) := by
      rw [show 1 - -(ε / (1 - ε)) = 1 / (1 - ε) by field_simp; ring,
        Real.sqrt_div' _ h1ε.le, Real.sqrt_one, one_div_one_div]
    rw [e1, e2]
    have hbase : Real.exp (ε / 2) * Real.sqrt (1 - ε) ≤ Real.exp (-(ε ^ 2 / 6)) := by
      have h1 : Real.sqrt (1 - ε) ≤ Real.sqrt (Real.exp (-ε - ε ^ 2 / 3)) :=
        Real.sqrt_le_sqrt (lower_ineq ε hε0.le hε)
      have h2 : Real.sqrt (Real.exp (-ε - ε ^ 2 / 3)) = Real.exp ((-ε - ε ^ 2 / 3) / 2) := by
        rw [← Real.sqrt_sq (Real.exp_pos ((-ε - ε ^ 2 / 3) / 2)).le, ← Real.exp_nat_mul]
        congr 2; push_cast; ring
      rw [h2] at h1
      calc Real.exp (ε / 2) * Real.sqrt (1 - ε)
          ≤ Real.exp (ε / 2) * Real.exp ((-ε - ε ^ 2 / 3) / 2) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = Real.exp (-(ε ^ 2 / 6)) := by rw [← Real.exp_add]; congr 1; ring
    calc Real.exp (ε * n / 2) * Real.sqrt (1 - ε) ^ n
        = (Real.exp (ε / 2) * Real.sqrt (1 - ε)) ^ n := by
          rw [mul_pow, ← Real.exp_nat_mul]; congr 2; ring
      _ ≤ (Real.exp (-(ε ^ 2 / 6))) ^ n :=
          pow_le_pow_left₀ (by positivity) hbase n
      _ = Real.exp (-(ε ^ 2 * n / 6)) := by rw [← Real.exp_nat_mul]; congr 1; ring
  calc μ {W | ε ≤ |S W / q - 1|}
      ≤ μ ({W | (1 + ε) * q ≤ S W} ∪ {W | -((1 - ε) * q) ≤ -S W}) := measure_mono hsub
    _ ≤ μ {W | (1 + ε) * q ≤ S W} + μ {W | -((1 - ε) * q) ≤ -S W} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-(ε ^ 2 * n / 6))) +
          ENNReal.ofReal (Real.exp (-(ε ^ 2 * n / 6))) := add_le_add hup hlow
    _ = ENNReal.ofReal (2 * Real.exp (-(ε ^ 2 * n / 6))) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]; ring_nf

end UnderstandingML.JLAux

open UnderstandingML UnderstandingML.JLAux in
theorem solution {d : ℕ} (Q : Finset (Fin d → ℝ)) (hQ : ∀ x ∈ Q, x ≠ 0) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ < 1) (n : ℕ) (hn : 0 < n)
    (hε : Real.sqrt (6 * Real.log (2 * Q.card / δ) / n) ≤ 3 / 4) :
    gaussianMatrixLaw n d (n : NNReal)⁻¹
      {W | ∃ x ∈ Q, Real.sqrt (6 * Real.log (2 * Q.card / δ) / n) ≤
        |sqNorm ((Matrix.of W).mulVec x) / sqNorm x - 1|} ≤ ENNReal.ofReal δ := by
  classical
  set ε := Real.sqrt (6 * Real.log (2 * Q.card / δ) / n) with hεdef
  rcases Q.eq_empty_or_nonempty with hQe | hQne
  · simp [hQe]
  have hcard : (1 : ℝ) ≤ Q.card := by exact_mod_cast hQne.card_pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have harg : 1 < 2 * (Q.card : ℝ) / δ := by rw [lt_div_iff₀ hδ]; nlinarith
  have hlog : 0 < Real.log (2 * Q.card / δ) := Real.log_pos harg
  have hεpos : 0 < ε := Real.sqrt_pos.mpr (by positivity)
  have hε2 : ε ^ 2 * n / 6 = Real.log (2 * Q.card / δ) := by
    rw [hεdef, Real.sq_sqrt (by positivity)]; field_simp
  have hexp : 2 * Real.exp (-(ε ^ 2 * n / 6)) = δ / Q.card := by
    rw [hε2, Real.exp_neg, Real.exp_log (by positivity)]; field_simp
  calc gaussianMatrixLaw n d (n : NNReal)⁻¹
        {W | ∃ x ∈ Q, ε ≤ |sqNorm ((Matrix.of W).mulVec x) / sqNorm x - 1|}
      = gaussianMatrixLaw n d (n : NNReal)⁻¹
          (⋃ x ∈ Q, {W | ε ≤ |sqNorm ((Matrix.of W).mulVec x) / sqNorm x - 1|}) := by
        congr 1; ext W; simp
    _ ≤ ∑ x ∈ Q, gaussianMatrixLaw n d (n : NNReal)⁻¹
          {W | ε ≤ |sqNorm ((Matrix.of W).mulVec x) / sqNorm x - 1|} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _x ∈ Q, ENNReal.ofReal (2 * Real.exp (-(ε ^ 2 * n / 6))) :=
        Finset.sum_le_sum (fun x hx => single_tail hn x (hQ x hx) ε hεpos hε)
    _ = (Q.card : ENNReal) * ENNReal.ofReal (δ / Q.card) := by
        rw [Finset.sum_const, nsmul_eq_mul, hexp]
    _ = ENNReal.ofReal δ := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1; field_simp
