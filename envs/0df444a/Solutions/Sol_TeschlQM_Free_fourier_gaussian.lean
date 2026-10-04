-- Prove2me | solution 1 for TeschlQM.Free.fourier_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T08:03:14.16601+00:00
-- url     : https://prove2.me/submissions/db05da41-8053-46cd-9838-8a67bd5ead66

import Mathlib
import Definitions.Def_TeschlQM_Free_fourier

set_option autoImplicit false

namespace TeschlA3cdb05c

open MeasureTheory

lemma iteratedDeriv_cexp_real (c : ℂ) (i : ℕ) :
    iteratedDeriv i (fun t : ℝ => Complex.exp (c * t)) =
      fun t : ℝ => c ^ i * Complex.exp (c * (t : ℂ)) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have h0 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := by
      simpa using (hasDerivAt_id t).ofReal_comp
    have h1 : HasDerivAt (fun t : ℝ => c * (t : ℂ)) (c * 1) t := h0.const_mul c
    have h2 := (h1.cexp).const_mul (c ^ i)
    rw [h2.deriv]
    ring

lemma poly_gauss_bound {a : ℝ} (ha : 0 < a) (m : ℕ) :
    ∃ K : ℝ, ∀ r : ℝ, 0 ≤ r → (1 + r) ^ m * Real.exp (-(a / 2) * r ^ 2) ≤ K := by
  set ε : ℝ := a / (4 * (m + 1)) with hε
  have hεpos : 0 < ε := by positivity
  refine ⟨Real.exp (a / 2) / ε ^ m, fun r hr => ?_⟩
  have hv0 : 0 ≤ 2 + 2 * r ^ 2 := by positivity
  have h1 : (1 + r) ^ m ≤ (2 + 2 * r ^ 2) ^ m := by
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [sq_nonneg (r - 1 / 4)]
  have h2 : (2 + 2 * r ^ 2) ≤ Real.exp (ε * (2 + 2 * r ^ 2)) / ε := by
    rw [le_div_iff₀ hεpos]
    have := Real.add_one_le_exp (ε * (2 + 2 * r ^ 2))
    nlinarith
  have h3 : (2 + 2 * r ^ 2) ^ m ≤ Real.exp (m * (ε * (2 + 2 * r ^ 2))) / ε ^ m := by
    calc (2 + 2 * r ^ 2) ^ m ≤ (Real.exp (ε * (2 + 2 * r ^ 2)) / ε) ^ m :=
          pow_le_pow_left₀ hv0 h2 m
      _ = _ := by rw [div_pow, ← Real.exp_nat_mul]
  have hq : (m : ℝ) / (m + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have h4 : (m : ℝ) * (ε * (2 + 2 * r ^ 2)) ≤ a / 2 + (a / 2) * r ^ 2 := by
    have : (m : ℝ) * (ε * (2 + 2 * r ^ 2)) = (a / 4 * (2 + 2 * r ^ 2)) * ((m : ℝ) / (m + 1)) := by
      rw [hε]; field_simp
    rw [this]
    calc (a / 4 * (2 + 2 * r ^ 2)) * ((m : ℝ) / (m + 1)) ≤ (a / 4 * (2 + 2 * r ^ 2)) * 1 :=
          mul_le_mul_of_nonneg_left hq (by positivity)
      _ = a / 2 + (a / 2) * r ^ 2 := by ring
  calc (1 + r) ^ m * Real.exp (-(a / 2) * r ^ 2)
      ≤ Real.exp (m * (ε * (2 + 2 * r ^ 2))) / ε ^ m * Real.exp (-(a / 2) * r ^ 2) := by
        gcongr; exact h1.trans h3
    _ ≤ Real.exp (a / 2 + (a / 2) * r ^ 2) / ε ^ m * Real.exp (-(a / 2) * r ^ 2) := by
        gcongr
    _ = Real.exp (a / 2) / ε ^ m := by
        rw [div_mul_eq_mul_div, ← Real.exp_add]; ring_nf

lemma gauss_schwartz (n : ℕ) (z : ℂ) (hz : 0 < z.re) :
    ∃ φ : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ,
        ∀ x, φ x = Complex.exp (-z * ((‖x‖ ^ 2 : ℝ) : ℂ) / 2) := by
  have hG : (fun x : EuclideanSpace ℝ (Fin n) => Complex.exp (-z * ((‖x‖ ^ 2 : ℝ) : ℂ) / 2)) =
      (fun t : ℝ => Complex.exp ((-z / 2) * t)) ∘ (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2) := by
    funext x; simp only [Function.comp]; congr 1; ring
  have hg : ∀ N : WithTop ℕ∞, ContDiff ℝ N (fun t : ℝ => Complex.exp ((-z / 2) * t)) := by
    intro N
    exact (Complex.contDiff_exp (𝕜 := ℝ)).comp (contDiff_const.mul Complex.ofRealCLM.contDiff)
  have hf : ∀ N : WithTop ℕ∞, ContDiff ℝ N (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2) :=
    fun N => contDiff_norm_sq ℝ
  refine ⟨⟨(fun t : ℝ => Complex.exp ((-z / 2) * t)) ∘
      (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2), (hg _).comp (hf _), ?_⟩,
      fun x => (congrFun hG x).symm⟩
  intro k m
  obtain ⟨k0, C0, hC0, hb⟩ :=
    (Function.hasTemperateGrowth_norm_sq (H := EuclideanSpace ℝ (Fin n))).norm_iteratedFDeriv_le_uniform m
  obtain ⟨K, hK⟩ := poly_gauss_bound hz (k + k0 * m)
  refine ⟨(m.factorial : ℝ) * (max 1 ‖-z / 2‖) ^ m * (max C0 1) ^ m * K, fun x => ?_⟩
  have hcomp := norm_iteratedFDeriv_comp_le (hg ⊤) (hf ⊤) (n := m) le_top x
    (C := (max 1 ‖-z / 2‖) ^ m * Real.exp (-(z.re / 2) * ‖x‖ ^ 2))
    (D := max C0 1 * (1 + ‖x‖) ^ k0) ?hC ?hD
  case hC =>
    intro i hi
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_cexp_real]
    have hre : ((-z / 2) * (((‖x‖ ^ 2 : ℝ)) : ℂ)).re = -(z.re / 2) * ‖x‖ ^ 2 := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
        Complex.div_ofNat_re, Complex.neg_re]; ring
    rw [norm_mul, norm_pow, Complex.norm_exp, hre]
    gcongr
    calc ‖-z / 2‖ ^ i ≤ (max 1 ‖-z / 2‖) ^ i :=
          pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) i
      _ ≤ (max 1 ‖-z / 2‖) ^ m := pow_le_pow_right₀ (le_max_left _ _) hi
  case hD =>
    intro i hi1 hin
    have hB : 1 ≤ max C0 1 * (1 + ‖x‖) ^ k0 :=
      one_le_mul_of_one_le_of_one_le (le_max_right _ _)
        (one_le_pow₀ (by linarith [norm_nonneg x]))
    calc ‖iteratedFDeriv ℝ i (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2) x‖
        ≤ C0 * (1 + ‖x‖) ^ k0 := hb i hin x
      _ ≤ max C0 1 * (1 + ‖x‖) ^ k0 := by gcongr; exact le_max_left _ _
      _ ≤ (max C0 1 * (1 + ‖x‖) ^ k0) ^ i := le_self_pow₀ hB (by omega)
  have hxk : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k :=
    pow_le_pow_left₀ (norm_nonneg _) (by linarith [norm_nonneg x]) k
  have hKx := hK ‖x‖ (norm_nonneg x)
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ m ((fun t : ℝ => Complex.exp ((-z / 2) * t)) ∘
          (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2)) x‖
      ≤ (1 + ‖x‖) ^ k * ((m.factorial : ℝ) * ((max 1 ‖-z / 2‖) ^ m *
          Real.exp (-(z.re / 2) * ‖x‖ ^ 2)) * (max C0 1 * (1 + ‖x‖) ^ k0) ^ m) :=
        mul_le_mul hxk hcomp (norm_nonneg _) (by positivity)
    _ = (m.factorial : ℝ) * (max 1 ‖-z / 2‖) ^ m * (max C0 1) ^ m *
          ((1 + ‖x‖) ^ (k + k0 * m) * Real.exp (-(z.re / 2) * ‖x‖ ^ 2)) := by
        rw [mul_pow, ← pow_mul, pow_add]; ring
    _ ≤ (m.factorial : ℝ) * (max 1 ‖-z / 2‖) ^ m * (max C0 1) ^ m * K := by
        gcongr

lemma cpow_ofReal_mul {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : w ≠ 0) (s : ℂ) :
    ((r : ℂ) * w) ^ s = (r : ℂ) ^ s * w ^ s := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hr' hw), Complex.log_ofReal_mul hr hw,
    Complex.cpow_def_of_ne_zero hr', Complex.cpow_def_of_ne_zero hw, ← Complex.exp_add,
    Complex.ofReal_log hr.le]
  ring_nf

lemma fourier_part (n : ℕ) (z : ℂ) (hz : 0 < z.re) :
    TeschlQM.Free.fourier n (fun x => Complex.exp (-z * ((‖x‖ ^ 2 : ℝ) : ℂ) / 2)) =
      fun p => ((z ^ (1 / 2 : ℂ)) ^ n)⁻¹ * Complex.exp (-((‖p‖ ^ 2 : ℝ) : ℂ) / (2 * z)) := by
  funext p
  have hz0 : z ≠ 0 := by
    intro h; rw [h] at hz; simp at hz
  have hb : 0 < (z / 2).re := by
    rw [Complex.div_ofNat_re]; linarith
  have hint := GaussianFourier.integral_cexp_neg_mul_sq_norm_add_of_euclideanSpace hb (-Complex.I) p
  have hcongr : (∫ x : EuclideanSpace ℝ (Fin n),
      Complex.exp (-((inner ℝ p x : ℝ) : ℂ) * Complex.I) *
        Complex.exp (-z * ((‖x‖ ^ 2 : ℝ) : ℂ) / 2)) =
      ∫ x : EuclideanSpace ℝ (Fin n),
        Complex.exp (-(z / 2) * ‖x‖ ^ 2 + (-Complex.I) * ((inner ℝ p x : ℝ) : ℂ)) := by
    congr 1; funext x; rw [← Complex.exp_add]; congr 1; push_cast; ring
  simp only [TeschlQM.Free.fourier]
  rw [hcongr, hint, Fintype.card_fin]
  have hexp : (-Complex.I) ^ 2 * (‖p‖ : ℂ) ^ 2 / (4 * (z / 2)) =
      -((‖p‖ ^ 2 : ℝ) : ℂ) / (2 * z) := by
    rw [neg_sq, Complex.I_sq]; push_cast; field_simp; ring
  have harg : z.arg ≠ Real.pi := (Complex.arg_lt_pi_iff.mpr (Or.inl hz.le)).ne
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have h1 : (Real.pi : ℂ) / (z / 2) = ((2 * Real.pi : ℝ) : ℂ) * z⁻¹ := by
    push_cast; field_simp
  have hpow : ((Real.pi : ℂ) / (z / 2)) ^ ((n : ℂ) / 2) =
      (((2 * Real.pi) ^ ((n : ℝ) / 2) : ℝ) : ℂ) * ((z ^ (1 / 2 : ℂ)) ^ n)⁻¹ := by
    rw [h1, cpow_ofReal_mul h2pi (inv_ne_zero hz0), Complex.inv_cpow z _ harg,
      Complex.ofReal_cpow h2pi.le]
    have e1 : (((n : ℝ) / 2 : ℝ) : ℂ) = (n : ℂ) / 2 := by push_cast; ring
    have e2 : (n : ℂ) / 2 = (n : ℂ) * (1 / 2) := by ring
    rw [e1, e2]
    simp only [Complex.cpow_nat_mul]
  rw [hpow, hexp]
  have hne : (((2 * Real.pi) ^ ((n : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < (2 * Real.pi) ^ ((n : ℝ) / 2) := Real.rpow_pos_of_pos h2pi _
    exact_mod_cast this.ne'
  field_simp

end TeschlA3cdb05c

open TeschlQM.Free MeasureTheory in
theorem solution (n : ℕ) (z : ℂ) (hz : 0 < z.re) :
    (∃ φ : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ,
        ∀ x, φ x = Complex.exp (-z * ((‖x‖ ^ 2 : ℝ) : ℂ) / 2)) ∧
      fourier n (fun x => Complex.exp (-z * ((‖x‖ ^ 2 : ℝ) : ℂ) / 2)) =
        fun p => ((z ^ (1 / 2 : ℂ)) ^ n)⁻¹ * Complex.exp (-((‖p‖ ^ 2 : ℝ) : ℂ) / (2 * z)) := by
  exact ⟨TeschlA3cdb05c.gauss_schwartz n z hz, TeschlA3cdb05c.fourier_part n z hz⟩
