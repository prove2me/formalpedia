-- Prove2me | solution 1 for TraceEstimation.ProjectionRank.chi_squared_tail
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-01T21:02:56.761161+00:00
-- url     : https://prove2.me/submissions/4e6e54b5-86b2-4786-894a-560a76c6a576

import Mathlib


open MeasureTheory ProbabilityTheory Real

namespace TraceGaussianProof

lemma gaussian_sq_mgf (a : ℝ) (ha : 2 * a < 1) :
    Integrable (fun x : ℝ => exp (a * x ^ 2)) (gaussianReal 0 1) ∧
      (∫ x : ℝ, exp (a * x ^ 2) ∂gaussianReal 0 1) =
        (1 - 2 * a) ^ (-(1 : ℝ) / 2) := by
  have hb : 0 < 1 / 2 - a := by linarith
  have hd : 0 < 1 - 2 * a := by linarith
  have hp : 0 < 2 * Real.pi := by positivity
  have hw : ∀ x : ℝ, gaussianPDFReal 0 1 x * exp (a * x ^ 2) =
      (sqrt (2 * Real.pi))⁻¹ * exp (-(1 / 2 - a) * x ^ 2) := by
    intro x
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    rw [mul_assoc, ← exp_add]
    congr 2
    ring
  have hwi : Integrable (fun x : ℝ => gaussianPDFReal 0 1 x * exp (a * x ^ 2)) := by
    simp_rw [hw]
    exact (integrable_exp_neg_mul_sq hb).const_mul _
  have hi : Integrable (fun x : ℝ => exp (a * x ^ 2)) (gaussianReal 0 1) := by
    rw [gaussianReal_of_var_ne_zero _ (one_ne_zero : (1 : NNReal) ≠ 0)]
    apply (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)).mpr
    simpa only [toReal_gaussianPDF, smul_eq_mul] using hwi
  refine ⟨hi, ?_⟩
  rw [integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : NNReal) ≠ 0)]
  simp_rw [smul_eq_mul, hw]
  rw [integral_const_mul, integral_gaussian]
  set R := (sqrt (2 * Real.pi))⁻¹ * sqrt (Real.pi / (1 / 2 - a))
  have hR : 0 ≤ R := by positivity
  have hsq : R ^ 2 * (1 - 2 * a) = 1 := by
    dsimp [R]
    rw [mul_pow, inv_pow, sq_sqrt hp.le, sq_sqrt (by positivity)]
    field_simp
  have hs : ((1 - 2 * a) ^ (-(1 : ℝ) / 2)) ^ 2 * (1 - 2 * a) = 1 := by
    rw [← rpow_natCast, ← rpow_mul hd.le]
    norm_num
    rw [rpow_neg_one, inv_mul_cancel₀ hd.ne']
  apply (sq_eq_sq₀ hR (rpow_nonneg hd.le _)).mp
  nlinarith

lemma gaussian_pi_sq_mgf {ι : Type*} [Fintype ι] (d : ι → ℝ)
    (hd : ∀ i, 2 * d i < 1) :
    Integrable (fun x : ι → ℝ => exp (∑ i, d i * x i ^ 2))
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) ∧
    (∫ x : ι → ℝ, exp (∑ i, d i * x i ^ 2)
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      ∏ i, (1 - 2 * d i) ^ (-(1 : ℝ) / 2) := by
  classical
  have hc := fun i => gaussian_sq_mgf (d i) (hd i)
  refine ⟨?_, ?_⟩
  · simp_rw [exp_sum]
    exact Integrable.fintype_prod_dep (fun i => (hc i).1)
  · simp_rw [exp_sum]
    rw [integral_fintype_prod_eq_prod (fun i (x : ℝ) => exp (d i * x ^ 2))]
    simp_rw [fun i => (hc i).2]

end TraceGaussianProof


open Real Set

namespace HutchinsonProof

lemma log_one_add_cubic (x : ℝ) (hx : 0 ≤ x) :
    log (1 + x) ≤ x - x ^ 2 / 2 + x ^ 3 / 3 := by
  let F := fun y : ℝ => y - y ^ 2 / 2 + y ^ 3 / 3 - log (1 + y)
  let D := fun y : ℝ => 1 - y + y ^ 2 - 1 / (1 + y)
  have hd : ∀ y ∈ Icc 0 x, HasDerivAt F (D y) y := by
    intro y hy
    have hp : 1 + y ≠ 0 := by linarith [hy.1]
    convert (((hasDerivAt_id y).sub ((hasDerivAt_pow 2 y).div_const 2)).add
      ((hasDerivAt_pow 3 y).div_const 3)).sub
        (((hasDerivAt_const y 1).add (hasDerivAt_id y)).log hp) using 1 <;>
      first | rfl | (dsimp [F, D]; ring)
  have hm : MonotoneOn F (Icc 0 x) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 x)
      (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt) ?_
    intro y hy
    have hy0 : 0 ≤ y := (interior_subset hy).1
    have hp : 0 < 1 + y := by linarith
    dsimp [D]
    rw [sub_nonneg]
    apply (div_le_iff₀ hp).mpr
    nlinarith [pow_nonneg hy0 3]
  have hh := hm ⟨le_rfl, hx⟩ ⟨hx, le_rfl⟩ hx
  simpa [F] using hh

lemma lower_poly_pos (h : ℝ) : 0 < 1 - h + 3 / 2 * h ^ 2 := by
  nlinarith [sq_nonneg (h - 1 / 3)]

lemma log_lower_poly (h : ℝ) (h0 : 0 ≤ h) (h1 : h ≤ 1 / 2) :
    log (1 - h + 3 / 2 * h ^ 2) ≤ -h + h ^ 2 + 4 / 3 * h ^ 3 := by
  let p := fun y : ℝ => 1 - y + 3 / 2 * y ^ 2
  let F := fun y : ℝ => -y + y ^ 2 + 4 / 3 * y ^ 3 - log (p y)
  let D := fun y : ℝ => -1 + 2 * y + 4 * y ^ 2 - (-1 + 3 * y) / p y
  have hd : ∀ y ∈ Icc 0 h, HasDerivAt F (D y) y := by
    intro y hy
    have hp := ((hasDerivAt_const y 1).sub (hasDerivAt_id y)).add
      ((hasDerivAt_pow 2 y).const_mul (3 / 2))
    convert ((((hasDerivAt_id y).neg.add (hasDerivAt_pow 2 y)).add
      ((hasDerivAt_pow 3 y).const_mul (4 / 3))).sub
        (hp.log (lower_poly_pos y).ne')) using 1 <;> first | rfl | (dsimp [F, D, p]; ring)
  have hm : MonotoneOn F (Icc 0 h) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 h)
      (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt) ?_
    intro y hy
    have hy0 : 0 ≤ y := (interior_subset hy).1
    have hy1 : y ≤ 1 / 2 := (interior_subset hy).2.trans h1
    have hp : 0 < p y := lower_poly_pos y
    dsimp [D]
    rw [sub_nonneg]
    apply (div_le_iff₀ hp).mpr
    dsimp [p]
    nlinarith [mul_nonneg (sq_nonneg y) (show 0 ≤ 1 / 2 - y by linarith), sq_nonneg (y ^ 2)]
  have hh := hm ⟨le_rfl, h0⟩ ⟨h0, le_rfl⟩ h0
  simpa [F, p] using hh

lemma lower_parameter_cost (ε : ℝ) (hε : 0 ≤ ε) :
    let h := ε / (2 * (1 + ε));
    -ε * h + h ^ 2 + 4 / 3 * h ^ 3 ≤ -(ε ^ 2 / 4 - ε ^ 3 / 6) := by
  dsimp
  have hp : 0 < 1 + ε := by linarith
  have he : -(ε ^ 2 / 4 - ε ^ 3 / 6) -
      (-ε * (ε / (2 * (1 + ε))) + (ε / (2 * (1 + ε))) ^ 2 +
        4 / 3 * (ε / (2 * (1 + ε))) ^ 3) =
      ε ^ 4 * (3 + 3 * ε + 2 * ε ^ 2) / (12 * (1 + ε) ^ 3) := by
    field_simp [hp.ne']
    ring
  rw [← sub_nonneg, he]
  positivity

lemma exp_neg_le_quadratic (x : ℝ) (hx : 0 ≤ x) : exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  let F := fun y : ℝ => 1 - y + y ^ 2 / 2 - exp (-y)
  let D := fun y : ℝ => -1 + y + exp (-y)
  have hd : ∀ y ∈ Icc 0 x, HasDerivAt F (D y) y := by
    intro y hy
    convert (((hasDerivAt_const y 1).sub (hasDerivAt_id y)).add
      ((hasDerivAt_pow 2 y).div_const 2)).sub ((hasDerivAt_id y).neg.exp) using 1 <;>
      first | rfl | (dsimp [F, D]; ring)
  have hm : MonotoneOn F (Icc 0 x) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 x)
      (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt) ?_
    intro y hy
    dsimp [D]
    linarith [add_one_le_exp (-y)]
  have hh := hm ⟨le_rfl, hx⟩ ⟨hx, le_rfl⟩ hx
  simpa [F] using hh

end HutchinsonProof


open Real Set

namespace ProjectionRankProof

lemma log_one_add_lower_quadratic (x : ℝ) (hx : 0 ≤ x) :
    x - x ^ 2 / 2 ≤ log (1 + x) := by
  let F := fun y : ℝ => log (1 + y) - y + y ^ 2 / 2
  let D := fun y : ℝ => 1 / (1 + y) - 1 + y
  have hd : ∀ y ∈ Icc 0 x, HasDerivAt F (D y) y := by
    intro y hy
    have hp : 1 + y ≠ 0 := by linarith [hy.1]
    convert ((((hasDerivAt_const y 1).add (hasDerivAt_id y)).log hp).sub
      (hasDerivAt_id y)).add ((hasDerivAt_pow 2 y).div_const 2) using 1 <;>
      first | rfl | (dsimp [F, D]; ring)
  have hm : MonotoneOn F (Icc 0 x) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 x)
      (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt) ?_
    intro y hy
    have hp : 0 < 1 + y := by linarith [(interior_subset hy).1]
    have he : D y = y ^ 2 / (1 + y) := by dsimp [D]; field_simp; ring
    rw [he]
    positivity
  have hh := hm ⟨le_rfl, hx⟩ ⟨hx, le_rfl⟩ hx
  dsimp [F] at hh
  simp only [add_zero, log_one, sub_zero, zero_pow (by decide : 2 ≠ 0), zero_div] at hh
  linarith

end ProjectionRankProof


open MeasureTheory ProbabilityTheory Real

namespace ProjectionRankProof

lemma gaussian_sum_sq_mgf {ι : Type*} [Fintype ι] (s : ℝ) (hs : 2 * s < 1) :
    Integrable (fun g : ι → ℝ => exp (s * ∑ l, g l ^ 2))
      (Measure.pi fun _ : ι => gaussianReal 0 1) ∧
    (∫ g : ι → ℝ, exp (s * ∑ l, g l ^ 2) ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      exp (-((Fintype.card ι : ℝ) / 2) * log (1 - 2 * s)) := by
  classical
  have hh := TraceGaussianProof.gaussian_pi_sq_mgf (fun _ : ι => s) (fun _ => hs)
  have hd : 0 < 1 - 2 * s := by linarith
  refine ⟨?_, ?_⟩
  · simpa only [← Finset.mul_sum] using hh.1
  · simp_rw [Finset.mul_sum]
    rw [hh.2]
    simp_rw [rpow_def_of_pos hd]
    rw [← exp_sum]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    congr 1
    ring

lemma chernoff_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (Z : Ω → ℝ) (s u b : ℝ) (hs : 0 ≤ s)
    (hi : Integrable (fun ω => exp (s * Z ω)) P) (hb : mgf Z P s ≤ exp b) :
    P.real {ω | u ≤ Z ω} ≤ exp (-s * u + b) := by
  calc
    P.real {ω | u ≤ Z ω} ≤ exp (-s * u) * mgf Z P s := measure_ge_le_exp_mul_mgf u hs hi
    _ ≤ exp (-s * u) * exp b := mul_le_mul_of_nonneg_left hb (exp_pos _).le
    _ = exp (-s * u + b) := (exp_add _ _).symm

lemma chi_tail (k : ℕ) (hk : 0 < k) (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    (Measure.pi fun _ : Fin k => gaussianReal 0 1).real
      {g | ε * k ≤ |∑ l, g l ^ 2 - k|} ≤ 2 * exp (-(k * ε ^ 2 / 6)) := by
  classical
  let P := Measure.pi fun _ : Fin k => gaussianReal 0 1
  let X := fun g : Fin k → ℝ => ∑ l, g l ^ 2
  haveI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  let t := ε / (2 * (1 + ε))
  have ht : 0 < t := by dsimp [t]; positivity
  have htE : t * (2 * (1 + ε)) = ε := by dsimp [t]; field_simp
  have ht' : 2 * t < 1 := by nlinarith [htE]
  have hum := gaussian_sum_sq_mgf (ι := Fin k) t ht'
  have huv : mgf X P t = exp (-((k : ℝ) / 2) * log (1 - 2 * t)) := by
    simpa only [mgf, X, P, Fintype.card_fin] using hum.2
  have huc : -t * ((k : ℝ) * (1 + ε)) + (-((k : ℝ) / 2) * log (1 - 2 * t)) ≤
      -((k : ℝ) * ε ^ 2 / 6) := by
    have he : 1 - 2 * t = (1 + ε)⁻¹ := by dsimp [t]; field_simp; ring
    rw [he, log_inv]
    have hc := mul_le_mul_of_nonneg_left (HutchinsonProof.log_one_add_cubic ε hε.le) hkpos.le
    have hh : 0 ≤ (k : ℝ) * (ε ^ 2 * (1 / 2 - ε)) :=
      mul_nonneg hkpos.le (mul_nonneg (sq_nonneg ε) (by linarith))
    nlinarith [htE]
  have hup : P.real {g | (k : ℝ) * (1 + ε) ≤ X g} ≤ exp (-((k : ℝ) * ε ^ 2 / 6)) :=
    (chernoff_bound P X t ((k : ℝ) * (1 + ε)) _ ht.le hum.1 huv.le).trans
      (exp_le_exp.mpr huc)
  let s := ε / 2
  have hs : 0 < s := by dsimp [s]; positivity
  have hlm := gaussian_sum_sq_mgf (ι := Fin k) (-s) (by linarith)
  have he : 1 - 2 * (-s) = 1 + ε := by dsimp [s]; ring
  have hlv : mgf (fun g => -X g) P s = exp (-((k : ℝ) / 2) * log (1 + ε)) := by
    have hh := hlm.2
    rw [he] at hh
    simpa only [mgf, X, P, Fintype.card_fin, neg_mul, mul_neg] using hh
  have hli : Integrable (fun g => exp (s * (-X g))) P := by
    simpa only [X, P, neg_mul, mul_neg] using hlm.1
  have hlc : -s * ((k : ℝ) * (ε - 1)) + (-((k : ℝ) / 2) * log (1 + ε)) ≤
      -((k : ℝ) * ε ^ 2 / 6) := by
    have hh := mul_le_mul_of_nonneg_left (log_one_add_lower_quadratic ε hε.le) hkpos.le
    dsimp [s]
    nlinarith [mul_nonneg hkpos.le (sq_nonneg ε)]
  have hlo : P.real {g | (k : ℝ) * (ε - 1) ≤ -X g} ≤ exp (-((k : ℝ) * ε ^ 2 / 6)) :=
    (chernoff_bound P (fun g => -X g) s ((k : ℝ) * (ε - 1)) _ hs.le hli hlv.le).trans
      (exp_le_exp.mpr hlc)
  have hsub : {g | ε * (k : ℝ) ≤ |X g - k|} ⊆
      {g | (k : ℝ) * (1 + ε) ≤ X g} ∪ {g | (k : ℝ) * (ε - 1) ≤ -X g} := by
    intro g hg
    change ε * (k : ℝ) ≤ |X g - k| at hg
    rcases le_abs.mp hg with h | h
    · left
      change (k : ℝ) * (1 + ε) ≤ X g
      nlinarith
    · right
      change (k : ℝ) * (ε - 1) ≤ -X g
      nlinarith
  calc
    P.real {g | ε * (k : ℝ) ≤ |X g - k|} ≤
      P.real ({g | (k : ℝ) * (1 + ε) ≤ X g} ∪ {g | (k : ℝ) * (ε - 1) ≤ -X g}) := measureReal_mono hsub
    _ ≤ P.real {g | (k : ℝ) * (1 + ε) ≤ X g} + P.real {g | (k : ℝ) * (ε - 1) ≤ -X g} :=
      measureReal_union_le _ _
    _ ≤ 2 * exp (-((k : ℝ) * ε ^ 2 / 6)) := by linarith

end ProjectionRankProof

open MeasureTheory ProbabilityTheory Real Matrix

theorem solution (k : ℕ) (hk : 0 < k) (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    (Measure.pi fun _ : Fin k => gaussianReal 0 1).real
        {g | ε * k ≤ |∑ l, g l ^ 2 - k|} ≤ 2 * Real.exp (-(k * ε ^ 2 / 6)) := by
  exact ProjectionRankProof.chi_tail k hk ε hε hε2
