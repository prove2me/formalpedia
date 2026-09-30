-- Prove2me | solution 1 for UnderstandingML.random_matrix_rip
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T14:47:10.053985+00:00
-- url     : https://prove2.me/submissions/30a1d03b-8ecf-48c8-a1ab-3ae227f5fb07

import Definitions.Def_UnderstandingML_DimReduction
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Nat.Choose.Bounds

open MeasureTheory ProbabilityTheory

namespace UnderstandingML.RIPAux


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


section NrmSection

variable {d : ℕ}

/-- The Euclidean norm `‖v‖₂ = √(∑ vᵢ²)`. -/
noncomputable def nrm (v : Fin d → ℝ) : ℝ := Real.sqrt (sqNorm v)

lemma nrm_nonneg (v : Fin d → ℝ) : 0 ≤ nrm v := Real.sqrt_nonneg _

lemma nrm_sq (v : Fin d → ℝ) : nrm v ^ 2 = sqNorm v := Real.sq_sqrt (sqNorm_nonneg v)

lemma nrm_eq_norm (v : Fin d → ℝ) : nrm v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖ := by
  rw [EuclideanSpace.norm_eq, nrm, sqNorm]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [Real.norm_eq_abs, sq_abs]

lemma nrm_add_le (u v : Fin d → ℝ) : nrm (u + v) ≤ nrm u + nrm v := by
  simp only [nrm_eq_norm, WithLp.toLp_add]
  exact norm_add_le _ _

lemma nrm_sum_le {ι : Type*} (s : Finset ι) (f : ι → Fin d → ℝ) :
    nrm (∑ j ∈ s, f j) ≤ ∑ j ∈ s, nrm (f j) := by
  simp only [nrm_eq_norm, WithLp.toLp_sum]
  exact norm_sum_le _ _

lemma sqNorm_eq_dot (v : Fin d → ℝ) : sqNorm v = v ⬝ᵥ v := by
  simp [sqNorm, dotProduct, sq]


lemma sqNorm_mulVec_orth {d : ℕ} (U : Matrix (Fin d) (Fin d) ℝ) (hU : U.transpose * U = 1)
    (v : Fin d → ℝ) : sqNorm (U.mulVec v) = sqNorm v := by
  rw [sqNorm_eq_dot, sqNorm_eq_dot, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    Matrix.mulVec_mulVec, hU, Matrix.one_mulVec, dotProduct_comm]

end NrmSection

/-! ### Nets on the unit sphere (volumetric argument) -/

section Net

variable {ι : Type*} [Fintype ι]

lemma packing_bound [Nonempty ι] (r : ℝ) (hr : 0 < r) (P : Finset (EuclideanSpace ℝ ι))
    (hP1 : ∀ p ∈ P, ‖p‖ = 1) (hsep : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → r < ‖p - q‖) :
    (P.card : ℝ) ≤ (1 + 2 / r) ^ Fintype.card ι := by
  classical
  set μ : Measure (EuclideanSpace ℝ ι) := volume with hμ
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ ι) = Fintype.card ι := finrank_euclideanSpace
  have hdisj : (P : Set (EuclideanSpace ℝ ι)).PairwiseDisjoint (fun p => Metric.ball p (r / 2)) := by
    intro p hp q hq hpq
    rw [Function.onFun, Set.disjoint_left]
    intro z hz1 hz2
    rw [Metric.mem_ball, dist_eq_norm] at hz1 hz2
    have h := hsep p hp q hq hpq
    have : ‖p - q‖ ≤ ‖z - p‖ + ‖z - q‖ := by
      calc ‖p - q‖ = ‖(z - q) - (z - p)‖ := by congr 1; abel
        _ ≤ ‖z - q‖ + ‖z - p‖ := norm_sub_le _ _
        _ = ‖z - p‖ + ‖z - q‖ := add_comm _ _
    linarith
  have hsub : (⋃ p ∈ P, Metric.ball p (r / 2)) ⊆ Metric.ball 0 (1 + r / 2) := by
    intro z hz
    simp only [Set.mem_iUnion, Metric.mem_ball, dist_eq_norm] at hz ⊢
    obtain ⟨p, hp, hzp⟩ := hz
    have := norm_le_insert' z p
    rw [sub_zero]
    have h1 : ‖z‖ ≤ ‖z - p‖ + ‖p‖ := by
      calc ‖z‖ = ‖(z - p) + p‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - p‖ + ‖p‖ := norm_add_le _ _
    rw [hP1 p hp] at h1
    linarith
  have hball : ∀ (x : EuclideanSpace ℝ ι) (t : ℝ), 0 ≤ t →
      μ (Metric.ball x t) = ENNReal.ofReal (t ^ Fintype.card ι) * μ (Metric.ball 0 1) := by
    intro x t ht
    rw [Measure.addHaar_ball μ x ht, hfin]
  have hV0 : μ (Metric.ball 0 1) ≠ 0 := (Metric.measure_ball_pos μ 0 one_pos).ne'
  have hVtop : μ (Metric.ball 0 1) ≠ ⊤ := measure_ball_lt_top.ne
  have key : (P.card : ENNReal) * ENNReal.ofReal ((r / 2) ^ Fintype.card ι) * μ (Metric.ball 0 1) ≤
      ENNReal.ofReal ((1 + r / 2) ^ Fintype.card ι) * μ (Metric.ball 0 1) := by
    calc (P.card : ENNReal) * ENNReal.ofReal ((r / 2) ^ Fintype.card ι) * μ (Metric.ball 0 1)
        = ∑ p ∈ P, μ (Metric.ball p (r / 2)) := by
          rw [Finset.sum_congr rfl (fun p _ => hball p (r / 2) (by positivity)), Finset.sum_const,
            nsmul_eq_mul, mul_assoc]
      _ = μ (⋃ p ∈ P, Metric.ball p (r / 2)) :=
          (measure_biUnion_finset hdisj (fun p _ => measurableSet_ball)).symm
      _ ≤ μ (Metric.ball 0 (1 + r / 2)) := measure_mono hsub
      _ = ENNReal.ofReal ((1 + r / 2) ^ Fintype.card ι) * μ (Metric.ball 0 1) :=
          hball 0 _ (by positivity)
  have key2 : (P.card : ENNReal) * ENNReal.ofReal ((r / 2) ^ Fintype.card ι) ≤
      ENNReal.ofReal ((1 + r / 2) ^ Fintype.card ι) :=
    (ENNReal.mul_le_mul_iff_left hV0 hVtop).mp key
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at key2
  have hr2 : 0 < (r / 2) ^ Fintype.card ι := by positivity
  have : (1 + 2 / r) ^ Fintype.card ι = (1 + r / 2) ^ Fintype.card ι / (r / 2) ^ Fintype.card ι := by
    rw [← div_pow]; congr 1; field_simp; ring
  rw [this, le_div_iff₀ hr2]
  exact key2

lemma exists_net (r : ℝ) (hr : 0 < r) :
    ∃ N : Finset (EuclideanSpace ℝ ι), (∀ q ∈ N, ‖q‖ = 1) ∧
      (N.card : ℝ) ≤ (1 + 2 / r) ^ Fintype.card ι ∧
      ∀ y : EuclideanSpace ℝ ι, ‖y‖ = 1 → ∃ q ∈ N, ‖y - q‖ ≤ r := by
  classical
  by_cases hι : IsEmpty ι
  · refine ⟨∅, by simp, by simp, ?_⟩
    intro y hy
    exfalso
    have : y = 0 := Subsingleton.elim _ _
    rw [this, norm_zero] at hy
    exact zero_ne_one hy
  haveI : Nonempty ι := not_isEmpty_iff.mp hι
  set B : ℕ := ⌊(1 + 2 / r) ^ Fintype.card ι⌋₊ with hB
  let Good : ℕ → Prop := fun k => ∃ P : Finset (EuclideanSpace ℝ ι), (∀ p ∈ P, ‖p‖ = 1) ∧
    (∀ p ∈ P, ∀ q ∈ P, p ≠ q → r < ‖p - q‖) ∧ P.card = k
  have hbound : ∀ k, Good k → k ≤ B := by
    rintro k ⟨P, hP1, hPsep, rfl⟩
    exact Nat.le_floor (packing_bound r hr P hP1 hPsep)
  have hG0 : Good 0 := ⟨∅, by simp, by simp, rfl⟩
  have hk := Nat.findGreatest_spec (P := Good) (Nat.zero_le B) hG0
  obtain ⟨P, hP1, hPsep, hPk⟩ := hk
  refine ⟨P, hP1, packing_bound r hr P hP1 hPsep, ?_⟩
  intro y hy
  by_contra hno
  push Not at hno
  have hyP : y ∉ P := by
    intro h
    have := hno y h
    simp at this
    linarith
  have hG : Good (Nat.findGreatest Good B + 1) := by
    refine ⟨insert y P, ?_, ?_, ?_⟩
    · intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact hy
      · exact hP1 p hp
    · intro p hp q hq hpq
      rcases Finset.mem_insert.mp hp with hpy | hp'
      · rcases Finset.mem_insert.mp hq with hqy | hq'
        · exact absurd (hpy.trans hqy.symm) hpq
        · rw [hpy]; exact hno q hq'
      · rcases Finset.mem_insert.mp hq with hqy | hq'
        · rw [hqy, norm_sub_rev]; exact hno p hp'
        · exact hPsep p hp' q hq' hpq
    · rw [Finset.card_insert_of_notMem hyP, hPk]
  have := Nat.le_findGreatest (hbound _ hG) hG
  omega

end Net

lemma sqNorm_smul {d : ℕ} (c : ℝ) (v : Fin d → ℝ) : sqNorm (c • v) = c ^ 2 * sqNorm v := by
  simp [sqNorm, mul_pow, Finset.mul_sum]

lemma nrm_sub_le {d : ℕ} (u v : Fin d → ℝ) : nrm (u - v) ≤ nrm u + nrm v := by
  simp only [nrm_eq_norm, WithLp.toLp_sub]
  exact norm_sub_le _ _

/-- Extension by zero from `EuclideanSpace ℝ I` to `Fin d → ℝ`. -/
noncomputable def embI {d : ℕ} (I : Finset (Fin d)) (y : EuclideanSpace ℝ I) : Fin d → ℝ :=
  fun i => if h : i ∈ I then y ⟨i, h⟩ else 0

lemma sqNorm_embI {d : ℕ} (I : Finset (Fin d)) (y : EuclideanSpace ℝ I) :
    sqNorm (embI I y) = ‖y‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, sqNorm]
  rw [← Finset.sum_subset (Finset.subset_univ I) (fun i _ hi => by simp [embI, hi])]
  rw [← Finset.sum_attach I, Finset.univ_eq_attach]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp [embI, j.2]

lemma embI_sub {d : ℕ} (I : Finset (Fin d)) (y q : EuclideanSpace ℝ I) :
    embI I (y - q) = embI I y - embI I q := by
  funext i
  by_cases h : i ∈ I <;> simp [embI, h]

/-- A net of the unit vectors supported on an index set `I`, inside `Fin d → ℝ`. -/
lemma exists_support_net {d : ℕ} (I : Finset (Fin d)) (r : ℝ) (hr : 0 < r) :
    ∃ N : Finset (Fin d → ℝ), (∀ v ∈ N, sqNorm v = 1) ∧
      (N.card : ℝ) ≤ (1 + 2 / r) ^ I.card ∧
      (∀ v ∈ N, ∀ i, i ∉ I → v i = 0) ∧
      ∀ x : Fin d → ℝ, (∀ i, i ∉ I → x i = 0) → sqNorm x = 1 →
        ∃ v ∈ N, nrm (x - v) ≤ r := by
  classical
  obtain ⟨N0, hN01, hN0card, hN0cov⟩ := exists_net (ι := I) r hr
  refine ⟨N0.image (embI I), ?_, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hv
    rw [sqNorm_embI, hN01 q hq, one_pow]
  · calc ((N0.image (embI I)).card : ℝ) ≤ N0.card := by exact_mod_cast Finset.card_image_le
      _ ≤ (1 + 2 / r) ^ Fintype.card I := hN0card
      _ = (1 + 2 / r) ^ I.card := by rw [Fintype.card_coe]
  · intro v hv i hi
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hv
    simp [embI, hi]
  · intro x hxI hx1
    set y : EuclideanSpace ℝ I := WithLp.toLp 2 (fun j => x j) with hy
    have hxy : embI I y = x := by
      funext i
      by_cases h : i ∈ I
      · simp [embI, h, hy]
      · simp [embI, h, hxI i h]
    have hy1 : ‖y‖ = 1 := by
      have := sqNorm_embI I y
      rw [hxy, hx1] at this
      have h0 := norm_nonneg y
      nlinarith
    obtain ⟨q, hq, hyq⟩ := hN0cov y hy1
    refine ⟨embI I q, Finset.mem_image_of_mem _ hq, ?_⟩
    rw [← hxy, ← embI_sub, nrm, sqNorm_embI, Real.sqrt_sq (norm_nonneg _)]
    exact hyq

/-- The deterministic core of Lemma 23.12: control on a fine net of the unit vectors supported on
`I` gives control on all vectors supported on `I`. -/
lemma rip_of_net {n d : ℕ} (M : Matrix (Fin n) (Fin d) ℝ) (I : Finset (Fin d)) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (N : Finset (Fin d → ℝ))
    (hNI : ∀ v ∈ N, ∀ i, i ∉ I → v i = 0)
    (hN : ∀ x : Fin d → ℝ, (∀ i, i ∉ I → x i = 0) → sqNorm x = 1 →
        ∃ v ∈ N, nrm (x - v) ≤ ε / 12)
    (hM : ∀ v ∈ N, |sqNorm (M.mulVec v) - 1| < ε / 6) :
    ∀ x : Fin d → ℝ, x ≠ 0 → (∀ i, i ∉ I → x i = 0) →
      |sqNorm (M.mulVec x) / sqNorm x - 1| ≤ ε := by
  classical
  intro x hx0 hxI
  set S : Set (Fin d → ℝ) := {x | ∀ i, i ∉ I → x i = 0} ∩ {x | sqNorm x = 1} with hS
  have hsqc : Continuous (fun x : Fin d → ℝ => sqNorm x) := by
    unfold sqNorm; fun_prop
  set g : (Fin d → ℝ) → ℝ := fun y => nrm (M.mulVec y) with hg
  have hgc : Continuous g := by
    have : Continuous fun x : Fin d → ℝ => M.mulVec x := by fun_prop
    have h2 : Continuous fun y => sqNorm (M.mulVec y) := by unfold sqNorm; fun_prop
    exact h2.sqrt
  have hSc : IsCompact S := by
    apply Metric.isCompact_of_isClosed_isBounded
    · apply IsClosed.inter
      · simp only [Set.setOf_forall]
        exact isClosed_iInter fun i => isClosed_iInter fun _ =>
          isClosed_eq (continuous_apply i) continuous_const
      · exact isClosed_eq hsqc continuous_const
    · rw [Metric.isBounded_iff_subset_closedBall 0]
      refine ⟨1, fun y hy => ?_⟩
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      rw [Real.norm_eq_abs, ← sq_le_one_iff_abs_le_one]
      have : y i ^ 2 ≤ sqNorm y :=
        Finset.single_le_sum (f := fun j => y j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      rw [hy.2] at this
      exact this
  -- normalization
  have hxpos : 0 < sqNorm x := sqNorm_pos hx0
  have hnx : 0 < nrm x := Real.sqrt_pos.mpr hxpos
  set u : Fin d → ℝ := (nrm x)⁻¹ • x with hu
  have hsqu : sqNorm u = 1 := by
    rw [hu, sqNorm_smul, inv_pow, nrm_sq, inv_mul_cancel₀ hxpos.ne']
  have huS : u ∈ S := ⟨fun i hi => by simp [hu, hxI i hi], hsqu⟩
  obtain ⟨x0, hx0S, hmax⟩ := hSc.exists_isMaxOn ⟨u, huS⟩ hgc.continuousOn
  set A := g x0 with hA
  have hA0 : 0 ≤ A := nrm_nonneg _
  have hbound : ∀ z : Fin d → ℝ, (∀ i, i ∉ I → z i = 0) → g z ≤ A * nrm z := by
    intro z hz
    by_cases hz0 : z = 0
    · simp [hg, hz0, nrm, sqNorm]
    have hzpos : 0 < sqNorm z := sqNorm_pos hz0
    have hnz : 0 < nrm z := Real.sqrt_pos.mpr hzpos
    have hmem : (nrm z)⁻¹ • z ∈ S := ⟨fun i hi => by simp [hz i hi], by
      show sqNorm ((nrm z)⁻¹ • z) = 1
      rw [sqNorm_smul, inv_pow, nrm_sq, inv_mul_cancel₀ hzpos.ne']⟩
    have h1 := hmax hmem
    simp only [Set.mem_setOf_eq] at h1
    have e : g ((nrm z)⁻¹ • z) = (nrm z)⁻¹ * g z := by
      simp only [hg, Matrix.mulVec_smul, nrm, sqNorm_smul]
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    rw [e, inv_mul_le_iff₀ hnz] at h1
    linarith
  -- approximation by the net
  have happrox : ∀ y ∈ S, ∃ t, 1 - ε / 6 ≤ t ∧ t ≤ 1 + ε / 12 ∧
      g y ≤ t + A * (ε / 12) ∧ t - A * (ε / 12) ≤ g y := by
    intro y hy
    obtain ⟨v, hv, hyv⟩ := hN y hy.1 hy.2
    have hsupp : ∀ i, i ∉ I → (y - v) i = 0 := by
      intro i hi; simp [hy.1 i hi, hNI v hv i hi]
    have hb := hbound (y - v) hsupp
    have hb' : g (y - v) ≤ A * (ε / 12) := le_trans hb (mul_le_mul_of_nonneg_left hyv hA0)
    refine ⟨nrm (M.mulVec v), ?_, ?_, ?_, ?_⟩
    · have h := hM v hv
      have h2 := nrm_sq (M.mulVec v)
      have h0 := nrm_nonneg (M.mulVec v)
      rw [abs_lt] at h
      nlinarith
    · have h := hM v hv
      have h2 := nrm_sq (M.mulVec v)
      have h0 := nrm_nonneg (M.mulVec v)
      rw [abs_lt] at h
      nlinarith
    · have : M.mulVec y = M.mulVec v + M.mulVec (y - v) := by
        rw [Matrix.mulVec_sub]; abel
      have h3 : g y ≤ nrm (M.mulVec v) + g (y - v) := by
        simp only [hg]; rw [this]; exact nrm_add_le _ _
      linarith
    · have : M.mulVec v = M.mulVec y - M.mulVec (y - v) := by
        rw [Matrix.mulVec_sub]; abel
      have h3 : nrm (M.mulVec v) ≤ g y + g (y - v) := by
        simp only [hg]; rw [this]; exact nrm_sub_le _ _
      linarith
  have hAub : A ≤ 1 + ε / 4 := by
    obtain ⟨t, -, ht2, ht3, -⟩ := happrox x0 hx0S
    nlinarith
  obtain ⟨t, ht1, ht2, ht3, ht4⟩ := happrox u huS
  have hgu0 : 0 ≤ g u := nrm_nonneg _
  have hlow : 1 - ε / 3 ≤ g u := by nlinarith
  have hup : g u ≤ 1 + ε / 4 := by nlinarith
  have hkey : sqNorm (M.mulVec x) / sqNorm x = g u ^ 2 := by
    simp only [hg, nrm_sq, hu, Matrix.mulVec_smul, sqNorm_smul, inv_pow, nrm_sq]
    field_simp
  rw [hkey, abs_le]
  constructor <;> nlinarith

end UnderstandingML.RIPAux

open UnderstandingML UnderstandingML.RIPAux in
theorem solution {d : ℕ} (U : Matrix (Fin d) (Fin d) ℝ) (hU : U.transpose * U = 1)
    (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1) (s : ℕ) (hs : 1 ≤ s)
    (hsd : s ≤ d) (n : ℕ) (hn : 216 * s * Real.log (72 * d / (δ * ε)) / ε ^ 2 ≤ n) :
    gaussianMatrixLaw n d (n : NNReal)⁻¹ {W | ¬ IsRIP ε s (Matrix.of W * U)} ≤
      ENNReal.ofReal δ := by
  classical
  have hdpos : 1 ≤ d := le_trans hs hsd
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hdpos
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hδε : δ * ε < 1 := by nlinarith
  have harg : 1 < 72 * (d : ℝ) / (δ * ε) := by
    rw [lt_div_iff₀ (by positivity)]; nlinarith
  have hlog : 0 < Real.log (72 * d / (δ * ε)) := Real.log_pos harg
  have hnpos : 0 < n := by
    have : 0 < 216 * (s : ℝ) * Real.log (72 * d / (δ * ε)) / ε ^ 2 := by positivity
    exact_mod_cast lt_of_lt_of_le this hn
  have hnet : ∀ I : Finset (Fin d), ∃ N : Finset (Fin d → ℝ), (∀ v ∈ N, sqNorm v = 1) ∧
      (N.card : ℝ) ≤ (1 + 2 / (ε / 12)) ^ I.card ∧
      (∀ v ∈ N, ∀ i, i ∉ I → v i = 0) ∧
      ∀ x : Fin d → ℝ, (∀ i, i ∉ I → x i = 0) → sqNorm x = 1 →
        ∃ v ∈ N, nrm (x - v) ≤ ε / 12 := fun I => exists_support_net I (ε / 12) (by positivity)
  choose NI hNI1 hNIcard hNIsupp hNIcov using hnet
  set bad : (Fin d → ℝ) → Set (Fin n → Fin d → ℝ) := fun y =>
    {W | ε / 6 ≤ |sqNorm ((Matrix.of W).mulVec y) / sqNorm y - 1|} with hbad
  have hsub : {W : Fin n → Fin d → ℝ | ¬ IsRIP ε s (Matrix.of W * U)} ⊆
      ⋃ I ∈ Finset.powersetCard s (Finset.univ : Finset (Fin d)), ⋃ v ∈ NI I, bad (U.mulVec v) := by
    intro W hW
    simp only [Set.mem_setOf_eq, IsRIP, not_forall] at hW
    obtain ⟨x, hx0, hxl0, hxbad⟩ := hW
    set T : Finset (Fin d) := Finset.univ.filter (fun i => x i ≠ 0) with hTdef
    have hT : T.card ≤ s := by
      have := hxl0; unfold l0Norm at this; convert this
    obtain ⟨I, hTI, -, hIcard⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ T) hT
      (by simpa using hsd)
    have hxI : ∀ i, i ∉ I → x i = 0 := by
      intro i hi
      by_contra h
      exact hi (hTI (by simp [hTdef, h]))
    by_contra hnot
    simp only [Set.mem_iUnion, not_exists] at hnot
    apply hxbad
    refine rip_of_net (Matrix.of W * U) I ε hε hε1 (NI I) (hNIsupp I) (hNIcov I) ?_ x hx0 hxI
    intro v hv
    have := hnot I (by simp [Finset.mem_powersetCard, hIcard]) v hv
    simp only [hbad, Set.mem_setOf_eq, not_le] at this
    rwa [sqNorm_mulVec_orth U hU, hNI1 I v hv, div_one, Matrix.mulVec_mulVec] at this
  set B : ℝ := (1 + 24 / ε) ^ s * (2 * Real.exp (-(ε ^ 2 * n / 216))) with hB
  have hone : ∀ I ∈ Finset.powersetCard s (Finset.univ : Finset (Fin d)),
      ∑ v ∈ NI I, gaussianMatrixLaw n d (n : NNReal)⁻¹ (bad (U.mulVec v)) ≤ ENNReal.ofReal B := by
    intro I hI
    rw [Finset.mem_powersetCard] at hI
    calc ∑ v ∈ NI I, gaussianMatrixLaw n d (n : NNReal)⁻¹ (bad (U.mulVec v))
        ≤ ∑ _v ∈ NI I, ENNReal.ofReal (2 * Real.exp (-(ε ^ 2 * n / 216))) := by
          apply Finset.sum_le_sum
          intro v hv
          have hUv : U.mulVec v ≠ 0 := by
            intro h0
            have := sqNorm_mulVec_orth U hU v
            rw [h0, hNI1 I v hv] at this
            simp [sqNorm] at this
          have := single_tail hnpos (U.mulVec v) hUv (ε / 6) (by positivity) (by linarith)
          have e : (ε / 6) ^ 2 * n / 6 = ε ^ 2 * n / 216 := by ring
          rw [e] at this
          exact this
      _ = ((NI I).card : ENNReal) * ENNReal.ofReal (2 * Real.exp (-(ε ^ 2 * n / 216))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ENNReal.ofReal ((1 + 24 / ε) ^ s) *
            ENNReal.ofReal (2 * Real.exp (-(ε ^ 2 * n / 216))) := by
          gcongr
          rw [← ENNReal.ofReal_natCast]
          apply ENNReal.ofReal_le_ofReal
          have := hNIcard I
          rw [hI.2] at this
          convert this using 3
          field_simp; ring
      _ = ENNReal.ofReal B := by
          rw [← ENNReal.ofReal_mul (by positivity)]
  -- the final numerical inequality
  have hfinal : ((d.choose s : ℕ) : ℝ) * B ≤ δ := by
    have hexp : Real.exp (-(ε ^ 2 * n / 216)) ≤ (δ * ε / (72 * d)) ^ s := by
      have h1 : (s : ℝ) * Real.log (72 * d / (δ * ε)) ≤ ε ^ 2 * n / 216 := by
        rw [div_le_iff₀ (by positivity)] at hn
        rw [le_div_iff₀ (by norm_num)]
        nlinarith
      calc Real.exp (-(ε ^ 2 * n / 216)) ≤ Real.exp (-((s : ℝ) * Real.log (72 * d / (δ * ε)))) :=
            Real.exp_le_exp.mpr (by linarith)
        _ = (δ * ε / (72 * d)) ^ s := by
            rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by positivity), ← inv_pow, inv_div]
    have hchoose : ((d.choose s : ℕ) : ℝ) ≤ (d : ℝ) ^ s := by
      exact_mod_cast Nat.choose_le_pow d s
    have h24 : 1 + 24 / ε ≤ 25 / ε := by
      have h1 : 1 ≤ 1 / ε := by rw [le_div_iff₀ hε]; linarith
      calc 1 + 24 / ε ≤ 1 / ε + 24 / ε := by linarith
        _ = 25 / ε := by ring
    have hq : 25 * δ / 72 ≤ 1 := by linarith
    calc ((d.choose s : ℕ) : ℝ) * B
        ≤ (d : ℝ) ^ s * ((25 / ε) ^ s * (2 * (δ * ε / (72 * d)) ^ s)) := by
          rw [hB]
          gcongr
      _ = 2 * ((d : ℝ) * (25 / ε) * (δ * ε / (72 * d))) ^ s := by
          rw [mul_pow, mul_pow]; ring
      _ = 2 * (25 * δ / 72) ^ s := by
          congr 2
          field_simp
      _ ≤ 2 * (25 * δ / 72) := by
          gcongr
          exact pow_le_of_le_one (by positivity) hq (by omega)
      _ ≤ δ := by linarith
  calc gaussianMatrixLaw n d (n : NNReal)⁻¹ {W | ¬ IsRIP ε s (Matrix.of W * U)}
      ≤ gaussianMatrixLaw n d (n : NNReal)⁻¹
          (⋃ I ∈ Finset.powersetCard s (Finset.univ : Finset (Fin d)), ⋃ v ∈ NI I, bad (U.mulVec v)) := measure_mono hsub
    _ ≤ ∑ I ∈ Finset.powersetCard s (Finset.univ : Finset (Fin d)),
          gaussianMatrixLaw n d (n : NNReal)⁻¹ (⋃ v ∈ NI I, bad (U.mulVec v)) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ I ∈ Finset.powersetCard s (Finset.univ : Finset (Fin d)),
          ∑ v ∈ NI I, gaussianMatrixLaw n d (n : NNReal)⁻¹ (bad (U.mulVec v)) :=
        Finset.sum_le_sum (fun I _ => measure_biUnion_finset_le _ _)
    _ ≤ ∑ _I ∈ Finset.powersetCard s (Finset.univ : Finset (Fin d)), ENNReal.ofReal B :=
        Finset.sum_le_sum hone
    _ = ENNReal.ofReal (((d.choose s : ℕ) : ℝ) * B) := by
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, ENNReal.ofReal_mul (q := B) (Nat.cast_nonneg (d.choose s)),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal hfinal
