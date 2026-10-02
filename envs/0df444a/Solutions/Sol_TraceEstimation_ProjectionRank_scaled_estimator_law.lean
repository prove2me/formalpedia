-- Prove2me | solution 1 for TraceEstimation.ProjectionRank.scaled_estimator_law
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-01T21:08:42.208825+00:00
-- url     : https://prove2.me/submissions/da244d01-0ed6-4557-b64a-ab2d59486684

import Mathlib
import Definitions.Def_TraceEstimation_Shared_gaussianEstimator


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
open scoped RealInnerProductSpace

namespace TraceGaussianProof

lemma quadratic_spectral {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (x : EuclideanSpace ℝ (Fin n)) :
    x ⬝ᵥ (A *ᵥ x) = ∑ i, hA.eigenvalues i * (hA.eigenvectorBasis.repr x i) ^ 2 := by
  let b := hA.eigenvectorBasis
  let G := Matrix.toEuclideanLin A
  have hs : G.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have heig : ∀ i, G (b i) = hA.eigenvalues i • b i := by
    intro i
    ext j
    exact congrFun (hA.mulVec_eigenvectorBasis i) j
  have hi : ⟪x, G x⟫ = ∑ i, hA.eigenvalues i * (b.repr x i) ^ 2 := by
    rw [← b.sum_inner_mul_inner x (G x)]
    apply Finset.sum_congr rfl
    intro i _
    have hh : ⟪b i, G x⟫ = hA.eigenvalues i * ⟪b i, x⟫ := by
      rw [← hs, heig, real_inner_smul_left]
    rw [hh, b.repr_apply_apply]
    rw [real_inner_comm x (b i)]
    ring
  rw [EuclideanSpace.inner_eq_star_dotProduct] at hi
  simp only [star_trivial] at hi
  change (A *ᵥ x) ⬝ᵥ x = ∑ i, hA.eigenvalues i * (b.repr x i) ^ 2 at hi
  rwa [dotProduct_comm] at hi

lemma single_sample_mgf {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (t : ℝ) (ht : ∀ i, 2 * hA.eigenvalues i * t < 1) :
    Integrable (fun x : Fin n → ℝ => exp (t * (x ⬝ᵥ (A *ᵥ x))))
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) ∧
    (∫ x : Fin n → ℝ, exp (t * (x ⬝ᵥ (A *ᵥ x)))
      ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1)) =
      ∏ i, (1 - 2 * hA.eigenvalues i * t) ^ (-(1 : ℝ) / 2) := by
  classical
  let b := hA.eigenvectorBasis
  have hc := gaussian_pi_sq_mgf (fun i => t * hA.eigenvalues i) (fun i => by
    convert ht i using 1 <;> ring)
  have hrepr : ∀ x : Fin n → ℝ,
      exp (t * ((∑ i, x i • b i : EuclideanSpace ℝ (Fin n)) ⬝ᵥ
        (A *ᵥ (∑ i, x i • b i : EuclideanSpace ℝ (Fin n))))) =
        exp (∑ i, (t * hA.eigenvalues i) * x i ^ 2) := by
    intro x
    rw [quadratic_spectral A hA, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have hx : (∑ j, x j • b j) = b.repr.symm (WithLp.toLp 2 x) := b.sum_repr_symm _
    rw [hx, LinearIsometryEquiv.apply_symm_apply]
    ring
  have hm : Measurable (fun x : Fin n → ℝ => ∑ i, x i • b i) :=
    Finset.measurable_sum _ (fun i _ => (measurable_pi_apply i).smul measurable_const)
  have he : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      exp (t * (x ⬝ᵥ (A *ᵥ x)))) (stdGaussian (EuclideanSpace ℝ (Fin n))) ∧
      (∫ x : EuclideanSpace ℝ (Fin n), exp (t * (x ⬝ᵥ (A *ᵥ x)))
        ∂stdGaussian (EuclideanSpace ℝ (Fin n))) =
        ∏ i, (1 - 2 * hA.eigenvalues i * t) ^ (-(1 : ℝ) / 2) := by
    rw [stdGaussian_eq_map_pi_orthonormalBasis b]
    refine ⟨?_, ?_⟩
    · rw [integrable_map_measure (by fun_prop) hm.aemeasurable]
      simpa only [Function.comp_def, hrepr] using hc.1
    · rw [integral_map hm.aemeasurable (by fun_prop)]
      simp only [hrepr]
      have hd : ∀ i, 1 - 2 * (t * hA.eigenvalues i) = 1 - 2 * hA.eigenvalues i * t := by
        intro i
        ring
      simpa only [hd] using hc.2
  rw [← map_pi_eq_stdGaussian (ι := Fin n)] at he
  have hi := (integrable_map_measure (by fun_prop) (by fun_prop)).mp he.1
  have hval := he.2
  rw [integral_map (by fun_prop) (by fun_prop)] at hval
  exact ⟨hi, hval⟩

lemma repeated_sample_mgf {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (M : ℕ) (hM : 0 < M) (t : ℝ)
    (ht : ∀ i, 2 * hA.eigenvalues i * t < 1) :
    Integrable (fun ω => exp (t * ((M : ℝ) * TraceEstimation.Shared.gaussianEstimator A M ω)))
      (TraceEstimation.Shared.gaussianSampleMeasure n M) ∧
    mgf (fun ω => (M : ℝ) * TraceEstimation.Shared.gaussianEstimator A M ω)
      (TraceEstimation.Shared.gaussianSampleMeasure n M) t =
      ∏ i, (1 - 2 * hA.eigenvalues i * t) ^ (-(M : ℝ) / 2) := by
  classical
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have he : ∀ ω : Fin M → Fin n → ℝ,
      t * ((M : ℝ) * TraceEstimation.Shared.gaussianEstimator A M ω) =
        ∑ j, t * (ω j ⬝ᵥ (A *ᵥ ω j)) := by
    intro ω
    simp only [TraceEstimation.Shared.gaussianEstimator, ← mul_assoc, mul_inv_cancel₀ hM0,
      one_mul, Finset.mul_sum]
  have hs := single_sample_mgf A hA t ht
  refine ⟨?_, ?_⟩
  · unfold TraceEstimation.Shared.gaussianSampleMeasure
    simp_rw [he, exp_sum]
    exact Integrable.fintype_prod_dep (fun _ : Fin M => hs.1)
  · unfold mgf TraceEstimation.Shared.gaussianSampleMeasure
    simp_rw [he, exp_sum]
    rw [integral_fintype_prod_eq_prod
      (fun (_ : Fin M) (x : Fin n → ℝ) => exp (t * (x ⬝ᵥ (A *ᵥ x))))]
    simp_rw [hs.2]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    have hp : 0 ≤ 1 - 2 * hA.eigenvalues i * t := by linarith [ht i]
    rw [← rpow_mul_natCast hp]
    congr 1
    ring

end TraceGaussianProof


open Matrix

namespace ProjectionRankProof

lemma projection_eigenvalues {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hA2 : A * A = A) (i : Fin n) : hA.eigenvalues i = 0 ∨ hA.eigenvalues i = 1 := by
  let e := Unitary.conjStarAlgAut ℝ (Matrix (Fin n) (Fin n) ℝ) hA.eigenvectorUnitary
  have hAe : A = e (diagonal hA.eigenvalues) := by simpa [e] using hA.spectral_theorem
  have hd : diagonal hA.eigenvalues * diagonal hA.eigenvalues = diagonal hA.eigenvalues := by
    apply e.injective
    rw [map_mul]
    change e (diagonal hA.eigenvalues) * e (diagonal hA.eigenvalues) = e (diagonal hA.eigenvalues)
    rw [← hAe]
    exact hA2
  have hi := congr_fun (congr_fun hd i) i
  simp only [diagonal_mul_diagonal, diagonal_apply_eq, Pi.mul_apply] at hi
  have hh : hA.eigenvalues i * (hA.eigenvalues i - 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hh with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

lemma projection_sum_eigenvalues {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hA2 : A * A = A) : (∑ i, hA.eigenvalues i) = (A.rank : ℝ) := by
  classical
  have hc := hA.rank_eq_card_non_zero_eigs
  have hne : ∀ i, hA.eigenvalues i ≠ 0 → hA.eigenvalues i = 1 := by
    intro i hi
    exact (projection_eigenvalues A hA hA2 i).resolve_left hi
  rw [hc]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun i => hA.eigenvalues i ≠ 0)]
  have hJ : ∀ i : {i : Fin n // hA.eigenvalues i ≠ 0}, hA.eigenvalues i = 1 := fun i => hne i i.property
  have hZ : ∀ i : {i : Fin n // ¬hA.eigenvalues i ≠ 0}, hA.eigenvalues i = 0 := fun i => not_not.mp i.property
  simp_rw [hJ, hZ]
  simp

lemma projection_trace_eq_rank {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hA2 : A * A = A) : A.trace = (A.rank : ℝ) :=
  hA.trace_eq_sum_eigenvalues.trans (projection_sum_eigenvalues A hA hA2)

end ProjectionRankProof


open MeasureTheory ProbabilityTheory Real Matrix
open TraceEstimation.Shared

namespace ProjectionRankProof

lemma projection_mgf {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hA2 : A * A = A) (M : ℕ) (hM : 0 < M) (t : ℝ) (ht : 2 * t < 1) :
    Integrable (fun ω => exp (t * ((M : ℝ) * gaussianEstimator A M ω))) (gaussianSampleMeasure n M) ∧
    mgf (fun ω => (M : ℝ) * gaussianEstimator A M ω) (gaussianSampleMeasure n M) t =
      exp (-((M : ℝ) * A.rank / 2) * log (1 - 2 * t)) := by
  classical
  have hd : 0 < 1 - 2 * t := by linarith
  have hdom : ∀ i, 2 * hA.eigenvalues i * t < 1 := by
    intro i
    rcases projection_eigenvalues A hA hA2 i with h | h
    · simp [h]
    · simpa [h] using ht
  have hh := TraceGaussianProof.repeated_sample_mgf A hA M hM t hdom
  refine ⟨hh.1, ?_⟩
  rw [hh.2]
  have hf : ∀ i, (1 - 2 * hA.eigenvalues i * t) ^ (-(M : ℝ) / 2) =
      exp ((-(M : ℝ) / 2 * log (1 - 2 * t)) * hA.eigenvalues i) := by
    intro i
    rcases projection_eigenvalues A hA hA2 i with h | h
    · simp [h]
    · simp only [h, mul_one, one_mul]
      rw [rpow_def_of_pos hd]
      congr 1
      ring
  simp_rw [hf]
  rw [← exp_sum, ← Finset.mul_sum, projection_sum_eigenvalues A hA hA2]
  congr 1
  ring

end ProjectionRankProof


open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace ProjectionRankProof

lemma map_eq_of_mgf_halfline {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : AEMeasurable X μ) (hY : AEMeasurable Y ν)
    (b : ℝ) (hb : 0 < b)
    (hXI : ∀ t < b, Integrable (fun ω => Real.exp (t * X ω)) μ)
    (hYI : ∀ t < b, Integrable (fun ω => Real.exp (t * Y ω)) ν)
    (hXY : ∀ t < b, mgf X μ t = mgf Y ν t) : μ.map X = ν.map Y := by
  have hXs : Iio b ⊆ interior (integrableExpSet X μ) := by
    have hh : Iio b ⊆ integrableExpSet X μ := fun t ht => hXI t ht
    simpa only [isOpen_Iio.interior_eq] using interior_mono hh
  have hYs : Iio b ⊆ interior (integrableExpSet Y ν) := by
    have hh : Iio b ⊆ integrableExpSet Y ν := fun t ht => hYI t ht
    simpa only [isOpen_Iio.interior_eq] using interior_mono hh
  have hXa : AnalyticOnNhd ℂ (complexMGF X μ) {z | z.re < b} :=
    analyticOnNhd_complexMGF.mono (fun z hz => hXs hz)
  have hYa : AnalyticOnNhd ℂ (complexMGF Y ν) {z | z.re < b} :=
    analyticOnNhd_complexMGF.mono (fun z hz => hYs hz)
  have hC : Set.EqOn (complexMGF X μ) (complexMGF Y ν) {z | z.re < b} := by
    refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hXa hYa
      ((convex_Iio b).linear_preimage Complex.reLm).isPreconnected
      (z₀ := (0 : ℂ)) (by simpa using hb) ?_
    have hE : ∀ᶠ x : ℝ in 𝓝[≠] (0 : ℝ), complexMGF X μ x = complexMGF Y ν x := by
      filter_upwards [(eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with x hx
      rw [complexMGF_ofReal, complexMGF_ofReal, hXY x hx]
    have h_real := hE.frequently
    rw [frequently_iff_seq_forall] at h_real ⊢
    obtain ⟨xs, hx_tendsto, hx_eq⟩ := h_real
    refine ⟨fun n => (xs n : ℂ), ?_, fun n => hx_eq n⟩
    rw [tendsto_nhdsWithin_iff] at hx_tendsto ⊢
    constructor
    · simpa only [Function.comp_def, Complex.ofReal_zero] using
        (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hx_tendsto.1
    · simpa using hx_tendsto.2
  apply Measure.ext_of_charFun
  ext t
  rw [← complexMGF_mul_I hX t, ← complexMGF_mul_I hY t]
  apply hC
  simpa using hb

end ProjectionRankProof


open MeasureTheory ProbabilityTheory Real Matrix
open TraceEstimation.Shared

namespace ProjectionRankProof

lemma scaled_law {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hA2 : A * A = A) (M : ℕ) (hM : 0 < M) :
    (gaussianSampleMeasure n M).map (fun ω => (M : ℝ) * gaussianEstimator A M ω) =
      (Measure.pi fun _ : Fin (M * A.rank) => gaussianReal 0 1).map (fun g => ∑ l, g l ^ 2) := by
  haveI : IsProbabilityMeasure (gaussianSampleMeasure n M) := by
    unfold gaussianSampleMeasure
    infer_instance
  refine map_eq_of_mgf_halfline _ _ _ _ (by unfold gaussianEstimator; fun_prop)
    (show AEMeasurable (fun g : Fin (M * A.rank) → ℝ => ∑ l, g l ^ 2)
      (Measure.pi fun _ => gaussianReal 0 1) from
      (show Measurable (fun g : Fin (M * A.rank) → ℝ => ∑ l, g l ^ 2) by fun_prop).aemeasurable)
    (1 / 2) (by norm_num) ?_ ?_ ?_
  · intro t ht
    exact (projection_mgf A hA hA2 M hM t (by linarith)).1
  · intro t ht
    exact (gaussian_sum_sq_mgf (ι := Fin (M * A.rank)) t (by linarith)).1
  · intro t ht
    rw [(projection_mgf A hA hA2 M hM t (by linarith)).2]
    have hh := (gaussian_sum_sq_mgf (ι := Fin (M * A.rank)) t (by linarith)).2
    simpa only [mgf, Fintype.card_fin, Nat.cast_mul] using hh.symm

end ProjectionRankProof

open MeasureTheory ProbabilityTheory Real Matrix
open TraceEstimation

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hA2 : A * A = A) (M : ℕ) (hM : 0 < M) :
    (Shared.gaussianSampleMeasure n M).map (fun ω => (M : ℝ) * Shared.gaussianEstimator A M ω) =
      (Measure.pi fun _ : Fin (M * A.rank) => gaussianReal 0 1).map
        (fun g => ∑ l, g l ^ 2) := by
  exact ProjectionRankProof.scaled_law A hA hA2 M hM
