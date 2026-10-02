-- Prove2me | solution 1 for ZudilinZeta.params13_kernel_saddle_limit_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-02T09:57:29.15935+00:00
-- url     : https://prove2.me/submissions/705379a0-437c-4c22-a3a8-013d34b12cba

import Definitions.Def_ZudilinZetaContourKernel
import Definitions.Def_Zeta23_GammaFacts_StirlingVert
import Theorems.Thm_ZudilinZeta_complex_stirling_right_half_plane
import Definitions.Def_ZudilinZetaAsymp
import Definitions.Def_ZudilinZetaParams13
import Mathlib

-- Component: missions.zudilin.StirlingPublicBridge
section
set_option autoImplicit false
noncomputable section
open Complex Filter Topology
namespace ZudilinZeta.GammaEstimates

def gammaExponent (w : ℂ) : ℂ := (w + 1 / 2) * Complex.log w - w

def normalizedGamma (w : ℂ) : ℂ :=
  Complex.Gamma (w + 1) * Complex.exp (-gammaExponent w) / Real.sqrt (2 * Real.pi)

def gammaError (w : ℂ) : ℂ := Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w

lemma normalizedGamma_ne_zero {w : ℂ} (hw : 0 < w.re) : normalizedGamma w ≠ 0 := by
  apply div_ne_zero
  · exact mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos (by simpa using (by linarith : 0 < w.re + 1)))
      (Complex.exp_ne_zero _)
  · exact Complex.ofReal_ne_zero.mpr (by positivity)

lemma hasDerivAt_gammaExponent {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt gammaExponent (Complex.log w + (1 / 2 : ℂ) / w) w := by
  have hw0 : w ≠ 0 := by intro h; simpa [h] using hw
  have h := (((hasDerivAt_id w).add_const (1 / 2 : ℂ)).fun_mul
    (Complex.hasDerivAt_log (Complex.mem_slitPlane_iff.mpr (Or.inl hw)))).sub (hasDerivAt_id w)
  convert! h using 1
  dsimp
  field_simp
  ring

lemma hasDerivAt_normalizedGamma {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt normalizedGamma (normalizedGamma w * gammaError w) w := by
  have hnot (m : ℕ) : w ≠ -(m : ℂ) := by
    intro h
    have := congrArg Complex.re h
    simp at this
    have : (0 : ℝ) ≤ m := by positivity
    linarith
  have hnot1 (m : ℕ) : w + 1 ≠ -(m : ℂ) := by
    intro h
    have := congrArg Complex.re h
    simp at this
    have : (0 : ℝ) ≤ m := by positivity
    linarith
  have hG : HasDerivAt (fun z : ℂ => Complex.Gamma (z + 1))
      (Complex.Gamma (w + 1) * Complex.digamma (w + 1)) w := by
    have h := (Complex.differentiableAt_Gamma (w + 1) hnot1).hasDerivAt.comp w
      ((hasDerivAt_id w).add_const 1)
    convert! h using 1
    simp only [mul_one]
    rw [Complex.digamma_def, logDeriv_apply]
    field_simp [Complex.Gamma_ne_zero hnot1]
  have he := ((hasDerivAt_gammaExponent hw).neg).cexp
  have hd := (hG.fun_mul he).div_const (Real.sqrt (2 * Real.pi) : ℂ)
  convert! hd using 1
  dsimp [normalizedGamma, gammaError]
  rw [Complex.digamma_apply_add_one w hnot]
  ring

lemma norm_normalizedGamma_sub_one_le_exp {w : ℂ} (hw : 1 ≤ w.re) :
    ‖normalizedGamma w - 1‖ ≤ Real.exp (2 / w.re) - 1 := by
  simpa only [normalizedGamma, gammaExponent] using
    ZudilinZeta.complex_stirling_right_half_plane w hw

lemma norm_normalizedGamma_sub_one_le {w : ℂ} (hw : 2 ≤ w.re) :
    ‖normalizedGamma w - 1‖ ≤ 4 / w.re := by
  have hwpos : 0 < w.re := by linarith
  have hsmall : |(2 : ℝ) / w.re| ≤ 1 := by
    rw [abs_of_pos (by positivity), div_le_one hwpos]
    exact hw
  calc
    ‖normalizedGamma w - 1‖ ≤ Real.exp (2 / w.re) - 1 :=
      norm_normalizedGamma_sub_one_le_exp (by linarith)
    _ ≤ |Real.exp (2 / w.re) - 1| := le_abs_self _
    _ ≤ 2 * |(2 : ℝ) / w.re| := Real.abs_exp_sub_one_le hsmall
    _ = 4 / w.re := by rw [abs_of_pos (by positivity)]; ring

lemma tendsto_normalizedGamma_of_re_tendsto_atTop {α : Type*} {l : Filter α} {w : α → ℂ}
    (hw : Tendsto (fun i => (w i).re) l atTop) :
    Tendsto (fun i => normalizedGamma (w i)) l (𝓝 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun i => 4 / (w i).re) l (𝓝 0) :=
    hw.const_div_atTop 4
  apply squeeze_zero' (Eventually.of_forall fun i => norm_nonneg _) _ hlim
  filter_upwards [hw.eventually (eventually_ge_atTop (2 : ℝ))] with i hi
  exact norm_normalizedGamma_sub_one_le hi

end ZudilinZeta.GammaEstimates
end
end

-- Component: missions.zudilin.GammaStirlingCorollaries
section
set_option autoImplicit false
noncomputable section
open Complex Filter Topology

namespace ZudilinZeta.GammaEstimates

lemma normalizedGamma_eq_standard {w : ℂ} (hw : w ≠ 0) :
    normalizedGamma w = Complex.Gamma w *
      Complex.exp (w - (w - 1 / 2) * Complex.log w) / (Real.sqrt (2 * Real.pi) : ℂ) := by
  rw [normalizedGamma, Complex.Gamma_add_one w hw]
  have he : -gammaExponent w = w - (w - 1 / 2) * Complex.log w - Complex.log w := by
    unfold gammaExponent
    ring
  rw [he, Complex.exp_sub, Complex.exp_log hw]
  field_simp

lemma Gamma_eq_stirling_mul_normalized {w : ℂ} (hw : w ≠ 0) :
    Complex.Gamma w = (Real.sqrt (2 * Real.pi) : ℂ) *
      Complex.exp ((w - 1 / 2) * Complex.log w - w) * normalizedGamma w := by
  rw [normalizedGamma_eq_standard hw]
  have hc : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have he : Complex.exp ((w - 1 / 2) * Complex.log w - w) *
      Complex.exp (w - (w - 1 / 2) * Complex.log w) = 1 := by
    rw [← Complex.exp_add, show (w - 1 / 2) * Complex.log w - w +
      (w - (w - 1 / 2) * Complex.log w) = 0 by ring, Complex.exp_zero]
  calc
    Complex.Gamma w = Complex.Gamma w *
      (Complex.exp ((w - 1 / 2) * Complex.log w - w) *
        Complex.exp (w - (w - 1 / 2) * Complex.log w)) := by rw [he, mul_one]
    _ = _ := by field_simp [hc]

lemma norm_normalizedGamma_scaled_sub_one_le {δ : ℝ} (hδ : 0 < δ)
    (n : ℕ) (hn : 2 ≤ (n : ℝ) * δ) {w : ℂ} (hw : δ ≤ w.re) :
    ‖normalizedGamma ((n : ℂ) * w) - 1‖ ≤ 4 / ((n : ℝ) * δ) := by
  have hnr : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hre : (n : ℝ) * δ ≤ ((n : ℂ) * w).re := by
    simpa using mul_le_mul_of_nonneg_left hw hnr
  exact (norm_normalizedGamma_sub_one_le (le_trans hn hre)).trans
    (div_le_div_of_nonneg_left (by norm_num) (by linarith) hre)

lemma tendsto_normalizedGamma_scaled {w : ℂ} (hw : 0 < w.re) :
    Tendsto (fun n : ℕ => normalizedGamma ((n : ℂ) * w)) atTop (𝓝 1) := by
  apply tendsto_normalizedGamma_of_re_tendsto_atTop
  have h := (tendsto_natCast_atTop_atTop :
    Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).atTop_mul_const hw
  simpa using h

end ZudilinZeta.GammaEstimates
end
end

-- Component: missions.zudilin.GammaProductAlgebra
section
set_option autoImplicit false
noncomputable section
open Complex Filter Topology

namespace ZudilinZeta.GammaEstimates

lemma balanced_gamma_product_exact {ι : Type*} (s : Finset ι)
    (v : ι → ℂ) (e : ι → ℤ) (n : ℕ) (hn : 0 < n)
    (hv : ∀ i ∈ s, v i ≠ 0)
    (hbalance : ∑ i ∈ s, (e i : ℂ) * v i = 0) :
    (∏ i ∈ s, Complex.Gamma ((n : ℂ) * v i) ^ e i) =
      (∏ i ∈ s, (Real.sqrt (2 * Real.pi) : ℂ) ^ e i) *
      Complex.exp ((n : ℂ) * (∑ i ∈ s, (e i : ℂ) * v i * Complex.log (v i)) -
        (∑ i ∈ s, (e i : ℂ)) / 2 * (Real.log (n : ℝ) : ℂ) -
        (1 / 2 : ℂ) * (∑ i ∈ s, (e i : ℂ) * Complex.log (v i))) *
      (∏ i ∈ s, normalizedGamma ((n : ℂ) * v i) ^ e i) := by
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hnc : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hterm (i : ι) (hi : i ∈ s) :
      Complex.Gamma ((n : ℂ) * v i) ^ e i =
        (Real.sqrt (2 * Real.pi) : ℂ) ^ e i *
        Complex.exp ((e i : ℂ) * (((n : ℂ) * v i - 1 / 2) *
          ((Real.log (n : ℝ) : ℂ) + Complex.log (v i)) - (n : ℂ) * v i)) *
        normalizedGamma ((n : ℂ) * v i) ^ e i := by
    rw [Gamma_eq_stirling_mul_normalized (mul_ne_zero hnc (hv i hi)),
      mul_zpow, mul_zpow, ← Complex.exp_int_mul]
    rw [show Complex.log ((n : ℂ) * v i) =
      (Real.log (n : ℝ) : ℂ) + Complex.log (v i) by
        simpa only [Complex.ofReal_natCast] using Complex.log_ofReal_mul hnr (hv i hi)]
  rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    ← Complex.exp_sum]
  congr 2
  apply congrArg Complex.exp
  calc
    (∑ i ∈ s, (e i : ℂ) * (((n : ℂ) * v i - 1 / 2) *
        ((Real.log (n : ℝ) : ℂ) + Complex.log (v i)) - (n : ℂ) * v i)) =
        ∑ i ∈ s, ((n : ℂ) * (Real.log (n : ℝ) : ℂ) * ((e i : ℂ) * v i) -
          (n : ℂ) * ((e i : ℂ) * v i) +
          (n : ℂ) * ((e i : ℂ) * v i * Complex.log (v i)) -
          (1 / 2 : ℂ) * (Real.log (n : ℝ) : ℂ) * (e i : ℂ) -
          (1 / 2 : ℂ) * ((e i : ℂ) * Complex.log (v i))) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        hbalance, mul_zero, zero_sub, neg_zero, zero_add]
      ring

end ZudilinZeta.GammaEstimates
end
end

-- Component: missions.zudilin.GammaSmallShifts
section
set_option autoImplicit false
noncomputable section
open Complex Filter Topology

namespace ZudilinZeta.GammaEstimates

def gammaSmallShiftFactor (w : ℂ) (s : ℤ) : ℂ :=
  if s = -1 then (w - 1)⁻¹ else if s = 0 then 1 else if s = 1 then w else w * (w + 1)

def gammaScaledShiftFactor (h v : ℂ) (s : ℤ) : ℂ :=
  if s = -1 then (v - h)⁻¹ else if s = 0 then 1 else if s = 1 then v else v * (v + h)

lemma Gamma_small_shift (w : ℂ) (hw : 2 ≤ w.re) (s : ℤ)
    (hs : s = -1 ∨ s = 0 ∨ s = 1 ∨ s = 2) :
    Complex.Gamma (w + (s : ℂ)) = Complex.Gamma w * gammaSmallShiftFactor w s := by
  have hw0 : w ≠ 0 := by intro he; norm_num [he] at hw
  have hwm : w - 1 ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    norm_num at hh
    linarith
  have hwp : w + 1 ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    norm_num at hh
    linarith
  rcases hs with rfl | rfl | rfl | rfl
  · norm_num [gammaSmallShiftFactor]
    have hh := Complex.Gamma_add_one (w - 1) hwm
    rw [sub_add_cancel] at hh
    apply (eq_div_iff hwm).mpr
    simpa only [sub_eq_add_neg, mul_comm] using hh.symm
  · simp [gammaSmallShiftFactor]
  · simpa [gammaSmallShiftFactor, mul_comm] using Complex.Gamma_add_one w hw0
  · norm_num [gammaSmallShiftFactor]
    rw [show w + 2 = (w + 1) + 1 by ring, Complex.Gamma_add_one (w + 1) hwp,
      Complex.Gamma_add_one w hw0]
    ring

lemma gammaSmallShiftFactor_scaled (x v : ℂ) (hx : x ≠ 0) (s : ℤ)
    (hs : s = -1 ∨ s = 0 ∨ s = 1 ∨ s = 2) :
    gammaSmallShiftFactor (x * v) s = x ^ s * gammaScaledShiftFactor x⁻¹ v s := by
  rcases hs with rfl | rfl | rfl | rfl
  · norm_num [gammaSmallShiftFactor, gammaScaledShiftFactor]
    rw [show x * v - 1 = x * (v - x⁻¹) by field_simp <;> ring, mul_inv]
  · simp [gammaSmallShiftFactor, gammaScaledShiftFactor]
  · simp [gammaSmallShiftFactor, gammaScaledShiftFactor]
  · norm_num [gammaSmallShiftFactor, gammaScaledShiftFactor]
    field_simp <;> ring

lemma prod_const_zpow {ι : Type*} (s : Finset ι) (e : ι → ℤ) {x : ℂ} (hx : x ≠ 0) :
    (∏ i ∈ s, x ^ e i) = x ^ (∑ i ∈ s, e i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, zpow_add₀ hx, ih]

lemma gamma_small_shift_product {ι : Type*} (s : Finset ι) (v : ι → ℂ)
    (e shift : ι → ℤ) (n : ℕ) (hn : 2 ≤ n)
    (hv : ∀ i ∈ s, 1 ≤ (v i).re)
    (hs : ∀ i ∈ s, shift i = -1 ∨ shift i = 0 ∨ shift i = 1 ∨ shift i = 2) :
    (∏ i ∈ s, Complex.Gamma ((n : ℂ) * v i + (shift i : ℂ)) ^ e i) =
      (∏ i ∈ s, Complex.Gamma ((n : ℂ) * v i) ^ e i) *
        (n : ℂ) ^ (∑ i ∈ s, shift i * e i) *
        (∏ i ∈ s, gammaScaledShiftFactor (n : ℂ)⁻¹ (v i) (shift i) ^ e i) := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have ht (i : ι) (hi : i ∈ s) :
      Complex.Gamma ((n : ℂ) * v i + (shift i : ℂ)) ^ e i =
        (Complex.Gamma ((n : ℂ) * v i) ^ e i * (n : ℂ) ^ (shift i * e i)) *
          gammaScaledShiftFactor (n : ℂ)⁻¹ (v i) (shift i) ^ e i := by
    have hre : 2 ≤ ((n : ℂ) * v i).re := by
      simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
      nlinarith [hv i hi]
    rw [Gamma_small_shift _ hre _ (hs i hi), gammaSmallShiftFactor_scaled _ _ hn0 _ (hs i hi),
      mul_zpow, mul_zpow, ← zpow_mul]
    ring
  rw [Finset.prod_congr rfl ht, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    prod_const_zpow _ _ hn0]

end ZudilinZeta.GammaEstimates
end
end

-- Component: missions.zudilin.SaddlePhase
section
set_option autoImplicit false

namespace ZudilinZeta

noncomputable def saddlePhase (P : Params) (τ : ℂ) : ℂ :=
  (P.r : ℂ)*(τ*Complex.log τ+
    ((P.eta 0 : ℂ)-τ)*Complex.log ((P.eta 0 : ℂ)-τ))+
  (∑ j ∈ Finset.Icc 1 P.q,
    ((τ-(P.eta 0 : ℂ)+(P.eta j : ℂ))*Complex.log (τ-(P.eta 0 : ℂ)+(P.eta j : ℂ))-
      (τ-(P.eta j : ℂ))*Complex.log (τ-(P.eta j : ℂ))))-
  2*(∑ j ∈ Finset.Icc 1 P.r, (P.eta j : ℂ)*Complex.log (P.eta j : ℂ))+
  ∑ j ∈ Finset.Icc (P.r+1) P.q,
    ((P.eta 0 : ℂ)-2*(P.eta j : ℂ))*Complex.log ((P.eta 0 : ℂ)-2*(P.eta j : ℂ))

noncomputable def saddlePhaseDeriv (P : Params) (τ : ℂ) : ℂ :=
  (P.r : ℂ)*(Complex.log τ-Complex.log ((P.eta 0 : ℂ)-τ))+
  ∑ j ∈ Finset.Icc 1 P.q,
    (Complex.log (τ-(P.eta 0 : ℂ)+(P.eta j : ℂ))-Complex.log (τ-(P.eta j : ℂ)))

lemma saddlePhase_sub_mul_deriv (P : Params) (τ : ℂ) :
    saddlePhase P τ-τ*saddlePhaseDeriv P τ=f0 P τ := by
  unfold saddlePhase saddlePhaseDeriv f0
  have hs :
      (∑ j ∈ Finset.Icc 1 P.q,
        ((τ-(P.eta 0 : ℂ)+(P.eta j : ℂ))*Complex.log (τ-(P.eta 0 : ℂ)+(P.eta j : ℂ))-
          (τ-(P.eta j : ℂ))*Complex.log (τ-(P.eta j : ℂ))))-
      τ*(∑ j ∈ Finset.Icc 1 P.q,
        (Complex.log (τ-(P.eta 0 : ℂ)+(P.eta j : ℂ))-Complex.log (τ-(P.eta j : ℂ))))=
      ∑ j ∈ Finset.Icc 1 P.q,
        ((P.eta j : ℂ)*Complex.log (τ-(P.eta j : ℂ))-
          ((P.eta 0 : ℂ)-(P.eta j : ℂ))*Complex.log (τ-(P.eta 0 : ℂ)+(P.eta j : ℂ))) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  linear_combination hs

private lemma complex_hasDerivAt_mul_log {z : ℂ} (hz : z∈Complex.slitPlane) :
    HasDerivAt (fun t : ℂ => t*Complex.log t) (Complex.log z+1) z := by
  convert! (hasDerivAt_id z).fun_mul (Complex.hasDerivAt_log hz) using 1
  simp only [id_eq, mul_one, one_mul, mul_inv_cancel₀ (Complex.slitPlane_ne_zero hz)]

lemma hasDerivAt_saddlePhase (P : Params) (τ : ℂ)
    (hτ : τ∈Complex.slitPlane)
    (h0 : (P.eta 0 : ℂ)-τ∈Complex.slitPlane)
    (hplus : ∀ j∈Finset.Icc 1 P.q,
      τ-(P.eta 0 : ℂ)+(P.eta j : ℂ)∈Complex.slitPlane)
    (hminus : ∀ j∈Finset.Icc 1 P.q, τ-(P.eta j : ℂ)∈Complex.slitPlane) :
    HasDerivAt (saddlePhase P) (saddlePhaseDeriv P τ) τ := by
  have hfirst : HasDerivAt
      (fun z : ℂ => (P.r : ℂ)*(z*Complex.log z+
        ((P.eta 0 : ℂ)-z)*Complex.log ((P.eta 0 : ℂ)-z)))
      ((P.r : ℂ)*(Complex.log τ-Complex.log ((P.eta 0 : ℂ)-τ))) τ := by
    convert! ((complex_hasDerivAt_mul_log hτ).add
      ((complex_hasDerivAt_mul_log h0).comp τ ((hasDerivAt_id τ).const_sub (P.eta 0 : ℂ)))).const_mul
        (P.r : ℂ) using 1 <;> first | rfl | ring
  have hsum : HasDerivAt
      (fun z : ℂ => ∑ j∈Finset.Icc 1 P.q,
        ((z-(P.eta 0 : ℂ)+(P.eta j : ℂ))*Complex.log (z-(P.eta 0 : ℂ)+(P.eta j : ℂ))-
          (z-(P.eta j : ℂ))*Complex.log (z-(P.eta j : ℂ))))
      (∑ j∈Finset.Icc 1 P.q,
        (Complex.log (τ-(P.eta 0 : ℂ)+(P.eta j : ℂ))-Complex.log (τ-(P.eta j : ℂ)))) τ := by
    apply HasDerivAt.fun_sum
    intro j hj
    convert! ((complex_hasDerivAt_mul_log (hplus j hj)).comp τ
      (((hasDerivAt_id τ).sub_const (P.eta 0 : ℂ)).add_const (P.eta j : ℂ))).sub
      ((complex_hasDerivAt_mul_log (hminus j hj)).comp τ
        ((hasDerivAt_id τ).sub_const (P.eta j : ℂ))) using 1 <;> first | rfl | ring
  exact ((hfirst.add hsum).sub_const _).add_const _

lemma exp_saddlePhaseDeriv (P : Params) (τ : ℂ)
    (hτ : τ≠0) (h0 : (P.eta 0 : ℂ)-τ≠0)
    (hplus : ∀ j∈Finset.Icc 1 P.q, τ-(P.eta 0 : ℂ)+(P.eta j : ℂ)≠0)
    (hminus : ∀ j∈Finset.Icc 1 P.q, τ-(P.eta j : ℂ)≠0) :
    Complex.exp (saddlePhaseDeriv P τ)=
      (τ^P.r*∏ j∈Finset.Icc 1 P.q, (τ-(P.eta 0 : ℂ)+(P.eta j : ℂ)))/
      (((P.eta 0 : ℂ)-τ)^P.r*∏ j∈Finset.Icc 1 P.q, (τ-(P.eta j : ℂ))) := by
  unfold saddlePhaseDeriv
  rw [Complex.exp_add, Complex.exp_nat_mul, Complex.exp_sub,
    Complex.exp_log hτ, Complex.exp_log h0, Complex.exp_sum]
  have hs :
      (∏ j∈Finset.Icc 1 P.q,
        Complex.exp (Complex.log (τ-(P.eta 0 : ℂ)+(P.eta j : ℂ))-
          Complex.log (τ-(P.eta j : ℂ))))=
      (∏ j∈Finset.Icc 1 P.q, (τ-(P.eta 0 : ℂ)+(P.eta j : ℂ)))/
      (∏ j∈Finset.Icc 1 P.q, (τ-(P.eta j : ℂ))) := by
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro j hj
    rw [Complex.exp_sub, Complex.exp_log (hplus j hj), Complex.exp_log (hminus j hj)]
  rw [hs, div_pow, div_mul_div_comm]

lemma exp_saddlePhaseDeriv_of_root (P : Params) (hr : P.r=3) (τ : ℂ)
    (him : 0<τ.im) (hroot : charPoly P τ=0) :
    Complex.exp (saddlePhaseDeriv P τ)=-1 := by
  have hτ : τ≠0 := by intro he; simpa [he] using him
  have h0 : (P.eta 0 : ℂ)-τ≠0 := by
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.natCast_im, Complex.zero_im, zero_sub, neg_eq_zero] at hi
    exact him.ne' hi
  have hreal (x : ℂ) (hx : x.im=0) : τ-x≠0 := by
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.sub_im, hx, Complex.zero_im, sub_zero] at hi
    exact him.ne' hi
  have hplus (j : ℕ) : τ-(P.eta 0 : ℂ)+(P.eta j : ℂ)≠0 := by
    rw [show τ-(P.eta 0 : ℂ)+(P.eta j : ℂ)=τ-((P.eta 0 : ℂ)-(P.eta j : ℂ)) by ring]
    apply hreal
    simp
  have hminus (j : ℕ) : τ-(P.eta j : ℂ)≠0 := hreal _ (by simp)
  rw [exp_saddlePhaseDeriv P τ hτ h0 (fun j _ => hplus j) (fun j _ => hminus j), hr]
  have hden : ((P.eta 0 : ℂ)-τ)^3*
      (∏ j∈Finset.Icc 1 P.q, (τ-(P.eta j : ℂ)))≠0 :=
    mul_ne_zero (pow_ne_zero _ h0) (Finset.prod_ne_zero_iff.mpr (fun j _ => hminus j))
  apply (div_eq_iff hden).mpr
  unfold charPoly at hroot
  rw [hr] at hroot
  have he := sub_eq_zero.mp hroot
  rw [← he]
  ring

end ZudilinZeta
end

-- Component: missions.zudilin.Params13GammaBases
section
set_option autoImplicit false
noncomputable section
open Complex Filter Topology

namespace ZudilinZeta

lemma params13GammaWeight_sum :
    ∑ i ∈ Finset.range 39, (params13GammaWeight i : ℂ) = 10 := by
  norm_num [params13GammaWeight, Finset.sum_range_succ]

lemma params13GammaBase_balance (z : ℂ) :
    ∑ i ∈ Finset.range 39, (params13GammaWeight i : ℂ) * params13GammaBase z i = 0 := by
  norm_num [params13GammaWeight, params13GammaBase, params13GammaSlope,
    params13GammaOffset, eta13, Finset.sum_range_succ]
  ring

lemma params13GammaBase_phase (z : ℂ) :
    (∑ i ∈ Finset.range 39,
      (params13GammaWeight i : ℂ) * params13GammaBase z i * Complex.log (params13GammaBase z i)) =
        saddlePhase params13 z := by
  norm_num [params13GammaWeight, params13GammaBase, params13GammaSlope,
    params13GammaOffset, eta13, Finset.sum_range_succ, saddlePhase, params13,
    Finset.sum_Icc_succ_top]
  ring

lemma params13GammaBase_re_ge_one {z : ℂ} (hz : 87 ≤ z.re ∧ z.re ≤ 175 / 2)
    (i : ℕ) (hi : i ∈ Finset.range 39) : 1 ≤ (params13GammaBase z i).re := by
  have hi' : i < 39 := Finset.mem_range.mp hi
  interval_cases i <;>
    norm_num [params13GammaWeight, params13GammaBase, params13GammaSlope,
      params13GammaOffset, eta13, Complex.mul_re] <;> linarith

lemma continuous_params13GammaBase (i : ℕ) : Continuous (fun z => params13GammaBase z i) := by
  unfold params13GammaBase
  fun_prop

lemma params13GammaBase_norm_le (z : ℂ) (i : ℕ) (hi : i ∈ Finset.range 39) :
    ‖params13GammaBase z i‖ ≤ ‖z‖ + 100 := by
  have hi' : i < 39 := Finset.mem_range.mp hi
  have hs : |params13GammaSlope i| ≤ 1 := by
    unfold params13GammaSlope
    split_ifs <;> norm_num
  have hc : |params13GammaOffset i| ≤ 100 := by
    interval_cases i <;> norm_num [params13GammaOffset, eta13]
  calc
    ‖params13GammaBase z i‖ ≤
        ‖(params13GammaSlope i : ℂ) * z‖ + ‖(params13GammaOffset i : ℂ)‖ := norm_add_le _ _
    _ = |params13GammaSlope i| * ‖z‖ + |params13GammaOffset i| := by
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ ‖z‖ + 100 := by nlinarith [mul_le_mul_of_nonneg_right hs (norm_nonneg z)]

lemma params13GammaBase_vertical_norm_le (τ : ℂ) (t : ℝ)
    (i : ℕ) (hi : i ∈ Finset.range 39) :
    ‖params13GammaBase (τ + (t : ℂ) * I) i‖ ≤ (‖τ‖ + 100) * (1 + |t|) := by
  have hz : ‖τ + (t : ℂ) * I‖ ≤ ‖τ‖ + |t| := by
    simpa only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      using norm_add_le τ ((t : ℂ) * I)
  have hb := params13GammaBase_norm_le (τ + (t : ℂ) * I) i hi
  nlinarith [abs_nonneg t, mul_nonneg (norm_nonneg τ) (abs_nonneg t)]

end ZudilinZeta
end
end

-- Component: missions.zudilin.GammaProductEstimates
section
set_option autoImplicit false
noncomputable section
open Complex Filter Topology

namespace ZudilinZeta.GammaEstimates

lemma normalizedGamma_scaled_norm_bounds {δ : ℝ} (hδ : 0 < δ)
    (n : ℕ) (hn : 8 ≤ (n : ℝ) * δ) {w : ℂ} (hw : δ ≤ w.re) :
    ‖normalizedGamma ((n : ℂ) * w)‖ ≤ 2 ∧
      ‖(normalizedGamma ((n : ℂ) * w))⁻¹‖ ≤ 2 := by
  have hh := norm_normalizedGamma_scaled_sub_one_le hδ n (by linarith) hw
  have he : ‖normalizedGamma ((n : ℂ) * w) - 1‖ ≤ 1 / 2 := by
    apply hh.trans
    apply (div_le_iff₀ (show 0 < (n : ℝ) * δ by linarith)).mpr
    linarith
  have hu := norm_sub_norm_le (normalizedGamma ((n : ℂ) * w)) (1 : ℂ)
  have hl := norm_sub_norm_le (1 : ℂ) (normalizedGamma ((n : ℂ) * w))
  rw [norm_one] at hu hl
  rw [norm_sub_rev] at hl
  have hlow : 1 / 2 ≤ ‖normalizedGamma ((n : ℂ) * w)‖ := by linarith
  refine ⟨by linarith, ?_⟩
  rw [norm_inv]
  have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hlow
  simpa using hh

lemma norm_zpow_le_of_norm_le_two {z : ℂ} (hz : ‖z‖ ≤ 2) (hi : ‖z⁻¹‖ ≤ 2)
    (e : ℤ) : ‖z ^ e‖ ≤ (2 : ℝ) ^ e.natAbs := by
  cases e with
  | ofNat m =>
    change ‖z ^ (m : ℤ)‖ ≤ (2 : ℝ) ^ m
    simpa only [zpow_natCast, norm_pow] using
      pow_le_pow_left₀ (norm_nonneg z) hz m
  | negSucc m =>
    simpa only [Int.natAbs_negSucc, zpow_negSucc, norm_inv, norm_pow, inv_pow] using
      pow_le_pow_left₀ (norm_nonneg z⁻¹) hi (m + 1)

lemma norm_prod_normalizedGamma_scaled_zpow_le {ι : Type*}
    (s : Finset ι) (v : ι → ℂ) (e : ι → ℤ) {δ : ℝ} (hδ : 0 < δ)
    (n : ℕ) (hn : 8 ≤ (n : ℝ) * δ) (hv : ∀ i ∈ s, δ ≤ (v i).re) :
    ‖∏ i ∈ s, normalizedGamma ((n : ℂ) * v i) ^ e i‖ ≤
      ∏ i ∈ s, (2 : ℝ) ^ (e i).natAbs := by
  rw [norm_prod]
  apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
  intro i hi
  obtain ⟨hu, hl⟩ := normalizedGamma_scaled_norm_bounds hδ n hn (hv i hi)
  exact norm_zpow_le_of_norm_le_two hu hl (e i)

lemma tendsto_normalizedGamma_scaled_moving {v : ℕ → ℂ} {w : ℂ}
    (hv : Tendsto v atTop (𝓝 w)) (hw : 0 < w.re) :
    Tendsto (fun n : ℕ => normalizedGamma ((n : ℂ) * v n)) atTop (𝓝 1) := by
  have he : ∀ᶠ n : ℕ in atTop, w.re / 2 ≤ (v n).re :=
    (Complex.continuous_re.tendsto w |>.comp hv).eventually
      (le_mem_nhds (by linarith : w.re / 2 < w.re))
  apply tendsto_normalizedGamma_of_re_tendsto_atTop
  apply tendsto_atTop_mono' atTop (f₁ := fun n : ℕ => (n : ℝ) * (w.re / 2))
  · filter_upwards [he] with n hn
    simpa only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero] using
      mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg (α := ℝ) n)
  · exact tendsto_natCast_atTop_atTop.atTop_mul_const (half_pos hw)

lemma tendsto_prod_normalizedGamma_scaled_moving_zpow {ι : Type*}
    (s : Finset ι) (v : ℕ → ι → ℂ) (w : ι → ℂ) (e : ι → ℤ)
    (hv : ∀ i ∈ s, Tendsto (fun n => v n i) atTop (𝓝 (w i)))
    (hw : ∀ i ∈ s, 0 < (w i).re) :
    Tendsto (fun n : ℕ => ∏ i ∈ s, normalizedGamma ((n : ℂ) * v n i) ^ e i)
      atTop (𝓝 1) := by
  have h := tendsto_finsetProd s (fun i hi =>
    (tendsto_normalizedGamma_scaled_moving (hv i hi) (hw i hi)).zpow₀ (e i) (by simp))
  simpa only [one_zpow, Finset.prod_const_one] using h

end ZudilinZeta.GammaEstimates
end
end

-- Component: missions.zudilin.GammaLeadingBounds
section
set_option autoImplicit false
noncomputable section
open Complex Filter Topology

namespace ZudilinZeta.GammaEstimates

lemma norm_zpow_le_of_norm_bounds {z : ℂ} {B : ℝ} (hz : ‖z‖ ≤ B) (hi : ‖z⁻¹‖ ≤ B)
    (e : ℤ) : ‖z ^ e‖ ≤ B ^ e.natAbs := by
  cases e with
  | ofNat m =>
    change ‖z ^ (m : ℤ)‖ ≤ B ^ m
    simpa only [zpow_natCast, norm_pow] using pow_le_pow_left₀ (norm_nonneg z) hz m
  | negSucc m =>
    simpa only [Int.natAbs_negSucc, zpow_negSucc, norm_inv, norm_pow, inv_pow] using
      pow_le_pow_left₀ (norm_nonneg z⁻¹) hi (m + 1)

lemma norm_exp_neg_half_log_bounds {z : ℂ} (hz : 1 ≤ ‖z‖) :
    ‖Complex.exp (-(1 / 2 : ℂ) * Complex.log z)‖ ≤ 1 ∧
      ‖(Complex.exp (-(1 / 2 : ℂ) * Complex.log z))⁻¹‖ ≤ ‖z‖ := by
  have hp : 0 < ‖z‖ := lt_of_lt_of_le zero_lt_one hz
  have hl : 0 ≤ Real.log ‖z‖ := Real.log_nonneg hz
  constructor
  · rw [Complex.norm_exp]
    have he : (-(1 / 2 : ℂ) * Complex.log z).re = -Real.log ‖z‖ / 2 := by
      simp [Complex.mul_re, Complex.log_re]
      ring
    rw [he]
    exact (Real.exp_le_one_iff).mpr (by linarith)
  · rw [← Complex.exp_neg, neg_mul, neg_neg, Complex.norm_exp]
    have he : ((1 / 2 : ℂ) * Complex.log z).re = Real.log ‖z‖ / 2 := by
      simp [Complex.mul_re, Complex.log_re]
      ring
    rw [he]
    exact (Real.exp_le_exp.mpr (by linarith : Real.log ‖z‖ / 2 ≤ Real.log ‖z‖)).trans
      (Real.exp_log hp).le

lemma norm_exp_weighted_log_le {ι : Type*} (s : Finset ι) (v : ι → ℂ)
    (e : ι → ℤ) {B : ℝ} (hB : 1 ≤ B)
    (hv : ∀ i ∈ s, 1 ≤ ‖v i‖ ∧ ‖v i‖ ≤ B) :
    ‖Complex.exp (-(1 / 2 : ℂ) * ∑ i ∈ s, (e i : ℂ) * Complex.log (v i))‖ ≤
      B ^ (∑ i ∈ s, (e i).natAbs) := by
  have he : Complex.exp (-(1 / 2 : ℂ) * ∑ i ∈ s, (e i : ℂ) * Complex.log (v i)) =
      ∏ i ∈ s, Complex.exp (-(1 / 2 : ℂ) * Complex.log (v i)) ^ e i := by
    rw [Finset.mul_sum, Complex.exp_sum]
    apply Finset.prod_congr rfl
    intro i _
    rw [← Complex.exp_int_mul]
    congr 1
    ring
  rw [he, norm_prod, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
  intro i hi
  obtain ⟨hu, hl⟩ := norm_exp_neg_half_log_bounds (hv i hi).1
  exact norm_zpow_le_of_norm_bounds (hu.trans hB) (hl.trans (hv i hi).2) (e i)

end ZudilinZeta.GammaEstimates
end
end

-- Component: missions.zudilin.Params13GammaProduct
section
set_option autoImplicit false
noncomputable section
open Complex Filter Topology

namespace ZudilinZeta
open GammaEstimates

def params13GammaCorrection (n : ℕ) (z : ℂ) : ℂ :=
  ∏ i ∈ Finset.range 39,
    normalizedGamma ((n : ℂ) * params13GammaBase z i) ^ params13GammaWeight i

def params13GammaLeading (z : ℂ) : ℂ :=
  Complex.exp (-(1 / 2 : ℂ) *
    ∑ i ∈ Finset.range 39, (params13GammaWeight i : ℂ) * Complex.log (params13GammaBase z i))

lemma params13GammaWeight_natAbs_sum :
    ∑ i ∈ Finset.range 39, (params13GammaWeight i).natAbs = 48 := by
  norm_num [params13GammaWeight, Finset.sum_range_succ]

lemma params13_gamma_constant_product :
    (∏ i ∈ Finset.range 39, (Real.sqrt (2 * Real.pi) : ℂ) ^ params13GammaWeight i) =
      (2 * (Real.pi : ℂ)) ^ 5 := by
  have hc : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hpow : (Real.sqrt (2 * Real.pi) : ℂ) ^ 2 = 2 * (Real.pi : ℂ) := by
    exact_mod_cast Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)
  calc
    _ = (Real.sqrt (2 * Real.pi) : ℂ) ^ 10 := by
      norm_num [params13GammaWeight, Finset.prod_range_succ]
      field_simp [hc] <;> ring
    _ = _ := by rw [show 10 = 2 * 5 by decide, pow_mul, hpow]

lemma params13_bare_gamma_product (n : ℕ) (hn : 0 < n) (z : ℂ)
    (hz : 87 ≤ z.re ∧ z.re ≤ 175 / 2) :
    (∏ i ∈ Finset.range 39, Complex.Gamma ((n : ℂ) * params13GammaBase z i) ^
      params13GammaWeight i) =
      ((2 * (Real.pi : ℂ)) ^ 5 / (n : ℂ) ^ 5) * Complex.exp ((n : ℂ) * saddlePhase params13 z) *
        params13GammaLeading z * params13GammaCorrection n z := by
  have hv (i : ℕ) (hi : i ∈ Finset.range 39) : params13GammaBase z i ≠ 0 := by
    intro he
    have hh := params13GammaBase_re_ge_one hz i hi
    norm_num [he] at hh
  rw [balanced_gamma_product_exact (Finset.range 39) (params13GammaBase z)
    params13GammaWeight n hn hv (params13GammaBase_balance z),
    params13_gamma_constant_product, params13GammaBase_phase, params13GammaWeight_sum]
  have he : Complex.exp (-(5 : ℂ) * (Real.log (n : ℝ) : ℂ)) = (n : ℂ) ^ (-5 : ℤ) := by
    have hh := Complex.exp_int_mul (Real.log (n : ℝ) : ℂ) (-5)
    simpa only [← Complex.ofReal_exp, Real.exp_log (Nat.cast_pos.mpr hn),
      Complex.ofReal_natCast, Int.cast_neg, Int.cast_ofNat] using hh
  rw [show (10 : ℂ) / 2 = 5 by norm_num, sub_eq_add_neg, sub_eq_add_neg,
    Complex.exp_add, Complex.exp_add, ← neg_mul, he]
  simp only [params13GammaLeading, params13GammaCorrection, zpow_neg, zpow_ofNat]
  ring

lemma tendsto_params13GammaCorrection_moving {v : ℕ → ℂ} {z : ℂ}
    (hv : Tendsto v atTop (𝓝 z)) (hz : 87 ≤ z.re ∧ z.re ≤ 175 / 2) :
    Tendsto (fun n => params13GammaCorrection n (v n)) atTop (𝓝 1) := by
  apply tendsto_prod_normalizedGamma_scaled_moving_zpow
    (Finset.range 39) (fun n i => params13GammaBase (v n) i)
    (params13GammaBase z) params13GammaWeight
  · intro i _
    exact (continuous_params13GammaBase i).tendsto z |>.comp hv
  · intro i hi
    linarith [params13GammaBase_re_ge_one hz i hi]

lemma norm_params13GammaCorrection_le (n : ℕ) (hn : 8 ≤ n) (z : ℂ)
    (hz : 87 ≤ z.re ∧ z.re ≤ 175 / 2) : ‖params13GammaCorrection n z‖ ≤ (2 : ℝ) ^ 48 := by
  have hn' : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have h := norm_prod_normalizedGamma_scaled_zpow_le (Finset.range 39)
    (params13GammaBase z) params13GammaWeight (δ := 1) zero_lt_one n
    (by simpa only [mul_one] using hn')
    (params13GammaBase_re_ge_one hz)
  simpa only [params13GammaCorrection, mul_one, Finset.prod_pow_eq_pow_sum,
    params13GammaWeight_natAbs_sum] using h

lemma norm_params13GammaLeading_le (z : ℂ) (hz : 87 ≤ z.re ∧ z.re ≤ 175 / 2) :
    ‖params13GammaLeading z‖ ≤ (‖z‖ + 100) ^ 48 := by
  have h := norm_exp_weighted_log_le (Finset.range 39) (params13GammaBase z)
    params13GammaWeight (B := ‖z‖ + 100) (by linarith [norm_nonneg z]) (by
      intro i hi
      exact ⟨(params13GammaBase_re_ge_one hz i hi).trans (Complex.re_le_norm _),
        params13GammaBase_norm_le z i hi⟩)
  simpa only [params13GammaLeading, params13GammaWeight_natAbs_sum] using h

lemma continuousAt_params13GammaLeading (z : ℂ) (hz : 87 ≤ z.re ∧ z.re ≤ 175 / 2) :
    ContinuousAt params13GammaLeading z := by
  apply ContinuousAt.cexp
  apply ContinuousAt.const_mul
  apply tendsto_finsetSum
  intro i hi
  apply ContinuousAt.const_mul
  apply ContinuousAt.comp (f := fun w => params13GammaBase w i)
    (continuousAt_clog (Complex.mem_slitPlane_iff.mpr (Or.inl (by
      linarith [params13GammaBase_re_ge_one hz i hi]))))
  exact (continuous_params13GammaBase i).continuousAt

end ZudilinZeta
end
end

-- Component: missions.zudilin.Params13GammaShift
section
set_option autoImplicit false
noncomputable section
open Complex Filter Topology Set

namespace ZudilinZeta

def params13GammaShiftConstant : ℂ :=
  (∏ j ∈ Finset.Icc 4 13, (91 - 2 * (eta13 j : ℂ))) / (27 : ℂ) ^ 6

def params13GammaShift (h z : ℂ) : ℂ :=
  (91 - 2 * z + 2 * h) * (91 - z) ^ 3 * (91 - z + h) ^ 3 *
    (∏ j ∈ Finset.Icc 1 13, (z - 91 + (eta13 j : ℂ) - h)⁻¹) * params13GammaShiftConstant

def params13GammaAmplitude (n : ℕ) (z : ℂ) : ℂ :=
  params13GammaShift (n : ℂ)⁻¹ z * params13GammaLeading z * params13GammaCorrection n z

def params13GammaLimitAmplitude (z : ℂ) : ℂ :=
  params13GammaShift 0 z * params13GammaLeading z

lemma eta13_real_bounds (j : ℕ) (hj : j ∈ Finset.Icc 1 13) :
    (27 : ℝ) ≤ eta13 j ∧ (eta13 j : ℝ) ≤ 38 := by
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
  interval_cases j <;> norm_num [eta13]

lemma params13_gamma_shift_denominator_re {z h : ℂ}
    (hz : 87 ≤ z.re ∧ z.re ≤ 175 / 2) (hh : h.re ≤ 1)
    (j : ℕ) (hj : j ∈ Finset.Icc 1 13) :
    1 ≤ (z - 91 + (eta13 j : ℂ) - h).re := by
  obtain ⟨he, _⟩ := eta13_real_bounds j hj
  norm_num [Complex.sub_re, Complex.add_re, Complex.natCast_re]
  linarith

lemma continuousAt_params13GammaShift (h z : ℂ)
    (hz : 87 ≤ z.re ∧ z.re ≤ 175 / 2) (hh : h.re ≤ 1) :
    ContinuousAt (fun p : ℂ × ℂ => params13GammaShift p.1 p.2) (h, z) := by
  have hp : ContinuousAt (fun p : ℂ × ℂ =>
      ∏ j ∈ Finset.Icc 1 13, (p.2 - 91 + (eta13 j : ℂ) - p.1)⁻¹) (h, z) := by
    apply tendsto_finsetProd
    intro j hj
    apply ContinuousAt.inv₀ (by fun_prop)
    intro he
    have hb := params13_gamma_shift_denominator_re hz hh j hj
    norm_num [he] at hb
  exact (((continuousAt_const.sub (continuousAt_const.mul continuousAt_snd)).add
    (continuousAt_const.mul continuousAt_fst)).mul
    ((continuousAt_const.sub continuousAt_snd).pow 3) |>.mul
    (((continuousAt_const.sub continuousAt_snd).add continuousAt_fst).pow 3) |>.mul hp).mul
    continuousAt_const

lemma tendsto_complex_nat_inv :
    Tendsto (fun n : ℕ => (n : ℂ)⁻¹) atTop (𝓝 0) := by
  have h := (tendsto_inv_atTop_zero.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)).ofReal
  simpa only [Function.comp_def, Complex.ofReal_inv, Complex.ofReal_natCast,
    Complex.ofReal_zero] using h

lemma tendsto_params13GammaAmplitude_moving {v : ℕ → ℂ} {z : ℂ}
    (hv : Tendsto v atTop (𝓝 z)) (hz : 87 ≤ z.re ∧ z.re ≤ 175 / 2) :
    Tendsto (fun n => params13GammaAmplitude n (v n)) atTop
      (𝓝 (params13GammaLimitAmplitude z)) := by
  have hs := (continuousAt_params13GammaShift 0 z hz (by norm_num)).tendsto.comp
    (tendsto_complex_nat_inv.prodMk_nhds hv)
  have hl := (continuousAt_params13GammaLeading z hz).tendsto.comp hv
  have hg := tendsto_params13GammaCorrection_moving hv hz
  simpa only [params13GammaAmplitude, params13GammaLimitAmplitude,
    Function.comp_def, mul_one] using (hs.mul hl).mul hg

lemma params13GammaLimitAmplitude_ne_zero (z : ℂ)
    (hz : 87 ≤ z.re ∧ z.re ≤ 175 / 2) : params13GammaLimitAmplitude z ≠ 0 := by
  have hline : (91 : ℂ) - 2 * z ≠ 0 := by
    intro he
    have hre := congrArg Complex.re he
    norm_num [Complex.mul_re] at hre
    linarith
  have hc : (91 : ℂ) - z ≠ 0 := by
    intro he
    have hre := congrArg Complex.re he
    norm_num at hre
    linarith
  have hden (j : ℕ) (hj : j ∈ Finset.Icc 1 13) : z - 91 + (eta13 j : ℂ) ≠ 0 := by
    have hb := params13_gamma_shift_denominator_re (h := 0) hz (by norm_num) j hj
    intro he
    norm_num [he] at hb
  have hconst : params13GammaShiftConstant ≠ 0 := by
    apply div_ne_zero
    · apply Finset.prod_ne_zero_iff.mpr
      intro j hj
      obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
      interval_cases j <;> norm_num [eta13]
    · norm_num
  unfold params13GammaLimitAmplitude params13GammaShift params13GammaLeading
  simp only [mul_zero, add_zero, sub_zero]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hline
    (pow_ne_zero 3 hc)) (pow_ne_zero 3 hc))
      (Finset.prod_ne_zero_iff.mpr fun j hj => inv_ne_zero (hden j hj))) hconst)
    (Complex.exp_ne_zero _)

lemma norm_params13GammaShift_le (h z : ℂ)
    (hz : 87 ≤ z.re ∧ z.re ≤ 175 / 2) (hh : ‖h‖ ≤ 1) :
    ‖params13GammaShift h z‖ ≤
      2 * (‖z‖ + 100) ^ 7 * ‖params13GammaShiftConstant‖ := by
  let K : ℝ := ‖z‖ + 100
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hline : ‖(91 : ℂ) - 2 * z + 2 * h‖ ≤ 2 * K := by
    have ha := norm_add_le ((91 : ℂ) - 2 * z) (2 * h)
    have hb := norm_sub_le (91 : ℂ) (2 * z)
    norm_num only [norm_mul, Complex.norm_ofNat] at ha hb
    dsimp [K]
    linarith
  have hc : ‖(91 : ℂ) - z‖ ≤ K := by
    have hh := norm_sub_le (91 : ℂ) z
    norm_num only [Complex.norm_ofNat] at hh
    dsimp [K]
    linarith
  have hc' : ‖(91 : ℂ) - z + h‖ ≤ K := by
    have ha := norm_add_le ((91 : ℂ) - z) h
    have hb := norm_sub_le (91 : ℂ) z
    norm_num only [Complex.norm_ofNat] at hb
    dsimp [K]
    linarith
  have hp : ‖∏ j ∈ Finset.Icc 1 13, (z - 91 + (eta13 j : ℂ) - h)⁻¹‖ ≤ 1 := by
    rw [norm_prod]
    apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
    intro j hj
    have hb := (params13_gamma_shift_denominator_re hz
      ((Complex.re_le_norm h).trans hh) j hj).trans (Complex.re_le_norm _)
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ hb
  unfold params13GammaShift
  simp only [norm_mul, norm_pow]
  calc
    _ ≤ (2 * K) * K ^ 3 * K ^ 3 * 1 * ‖params13GammaShiftConstant‖ := by
      gcongr
    _ = _ := by dsimp [K]; ring

end ZudilinZeta
end
end

-- Component: missions.zudilin.SaddleArctanBounds
section
set_option autoImplicit false

namespace ZudilinZeta

lemma arctan_cubic_lower (x : ℝ) (hx : 0 ≤ x) :
    x-x^3/3 ≤ Real.arctan x := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => Real.arctan t-(t-t^3/3))
      (t^4/(1+t^2)) t := by
    convert (Real.hasDerivAt_arctan t).sub
      ((hasDerivAt_id t).sub (((hasDerivAt_id t).pow 3).div_const 3)) using 1 <;>
      (first | rfl | (simp only [id_eq]; field_simp; ring))
  have hm := monotone_of_hasDerivAt_nonneg hd (fun t => by positivity)
  have hh := hm hx
  norm_num at hh
  linarith only [hh]

lemma arctan_quintic_upper (x : ℝ) (hx : 0 ≤ x) :
    Real.arctan x ≤ x-x^3/3+x^5/5 := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => t-t^3/3+t^5/5-Real.arctan t)
      (t^6/(1+t^2)) t := by
    convert (((hasDerivAt_id t).sub (((hasDerivAt_id t).pow 3).div_const 3)).add
      (((hasDerivAt_id t).pow 5).div_const 5)).sub (Real.hasDerivAt_arctan t) using 1 <;>
      (first | rfl | (simp only [id_eq]; field_simp; ring))
  have hm := monotone_of_hasDerivAt_nonneg hd (fun t => by positivity)
  have hh := hm hx
  norm_num at hh
  linarith only [hh]

lemma arctan_rational_enclosure (x l u a b : ℝ) (hl : 0 ≤ l)
    (hx : l ≤ x ∧ x ≤ u) (ha : a ≤ l-l^3/3) (hb : u-u^3/3+u^5/5 ≤ b) :
    a ≤ Real.arctan x ∧ Real.arctan x ≤ b :=
  ⟨ha.trans ((arctan_cubic_lower l hl).trans (Real.arctan_le_arctan_iff.mpr hx.1)),
    (Real.arctan_le_arctan_iff.mpr hx.2).trans
      ((arctan_quintic_upper u (hl.trans (hx.1.trans hx.2))).trans hb)⟩

lemma arg_eq_arctan_of_re_pos (z : ℂ) (hr : 0 < z.re) :
    z.arg = Real.arctan (z.im/z.re) := by
  have hh := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hr))
  rw [← Complex.tan_arg, Real.arctan_tan hh.1 hh.2]

lemma arctan_complement_quarter (y d : ℝ) (hy : 0 < y) (hyd : y < d) :
    Real.arctan (y/d) = Real.pi/4-Real.arctan ((d-y)/(d+y)) := by
  have hd : 0<d := hy.trans hyd
  have hdy : 0<d+y := by linarith
  have hm : (d-y)/(d+y)*(y/d)<1 := by
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hd).mpr
    simp only [one_mul]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hdy).mpr
    nlinarith only [sq_pos_of_pos hd, sq_nonneg y]
  have hh := Real.arctan_add hm
  have he : ((d-y)/(d+y)+y/d)/(1-(d-y)/(d+y)*(y/d))=1 := by
    have hn : 1-(d-y)/(d+y)*(y/d)≠0 := by linarith only [hm]
    apply (div_eq_one_iff_eq hn).mpr
    field_simp
    ring
  rw [he, Real.arctan_one] at hh
  linarith only [hh]

end ZudilinZeta
end

-- Component: missions.zudilin.Params13SaddlePolynomial
section
set_option autoImplicit false

namespace ZudilinZeta

def saddleQ13 (z : ℂ) : ℂ :=
  156*z^7-3872772*z^6+24237617292*z^5+11108559262764*z^4-
    287944618363648812*z^3-265165318728339296652*z^2-
    51416459087006412317436*z-1758025644874743176035740

lemma charPoly_params13_reduction (τ : ℂ) :
    65536*charPoly params13 τ = (2*τ-91)*saddleQ13 ((2*τ-91)^2) := by
  norm_num [charPoly, params13, eta13, Finset.prod_Icc_succ_top, saddleQ13]
  ring

lemma charPoly_params13_reflection (τ : ℂ) :
    charPoly params13 (91-τ) = -charPoly params13 τ := by
  apply mul_left_cancel₀ (a := (65536 : ℂ)) (by norm_num)
  rw [charPoly_params13_reduction, mul_neg, charPoly_params13_reduction]
  rw [show 2*((91 : ℂ)-τ)-91= -(2*τ-91) by ring, neg_sq]
  ring

end ZudilinZeta
end

-- Component: missions.zudilin.Params13RealRoots
section
set_option autoImplicit false

open Polynomial

namespace ZudilinZeta

noncomputable def saddleP13 : ℝ[X] :=
  X^7 - C (3872772/156) * X^6 + C (24237617292/156) * X^5 +
    C (11108559262764/156) * X^4 - C (287944618363648812/156) * X^3 -
    C (265165318728339296652/156) * X^2 - C (51416459087006412317436/156) * X -
    C (1758025644874743176035740/156)

lemma saddleP13_natDegree : saddleP13.natDegree = 7 := by
  unfold saddleP13
  compute_degree!

lemma saddleP13_monic : saddleP13.Monic := by
  unfold saddleP13
  monicity!

lemma saddleP13_complex (z : ℂ) : 156 * aeval z saddleP13 = saddleQ13 z := by
  simp [saddleP13, saddleQ13]
  ring

noncomputable def saddleRootLo (i : Fin 5) : ℝ :=
  ![-249790860432482171939476, -68538486020573165705126,
    -21108648548036042162859, -4348103402618084547975,
    1425404304483852874150593] i / 100000000000000000000

noncomputable def saddleRootHi (i : Fin 5) : ℝ :=
  ![-249790860432482171939475, -68538486020573165705125,
    -21108648548036042162858, -4348103402618084547974,
    1425404304483852874150594] i / 100000000000000000000

lemma saddleRoot_intervals (i : Fin 5) : saddleRootLo i < saddleRootHi i := by
  fin_cases i <;> norm_num [saddleRootLo, saddleRootHi]

lemma saddleRoot_intervals_disjoint (i j : Fin 5) (hij : i < j) :
    saddleRootHi i < saddleRootLo j := by
  fin_cases i <;> fin_cases j <;>
    (solve | norm_num at hij | norm_num [saddleRootLo, saddleRootHi])

lemma saddleP13_endpoint_signs (i : Fin 5) :
    (saddleP13.eval (saddleRootLo i) < 0 ∧ 0 < saddleP13.eval (saddleRootHi i)) ∨
    (saddleP13.eval (saddleRootHi i) < 0 ∧ 0 < saddleP13.eval (saddleRootLo i)) := by
  fin_cases i <;> norm_num [saddleP13, saddleRootLo, saddleRootHi]

lemma saddleP13_real_roots : ∃ r : Fin 5 → ℝ,
    StrictMono r ∧ (∀ i, r i ∈ Set.Icc (saddleRootLo i) (saddleRootHi i)) ∧
    ∀ i, saddleP13.eval (r i) = 0 := by
  have h (i : Fin 5) : ∃ x ∈ Set.Icc (saddleRootLo i) (saddleRootHi i),
      saddleP13.eval x = 0 := by
    rcases saddleP13_endpoint_signs i with h | h
    · exact intermediate_value_Icc (saddleRoot_intervals i).le
        saddleP13.continuous.continuousOn ⟨h.1.le, h.2.le⟩
    · exact intermediate_value_Icc' (saddleRoot_intervals i).le
        saddleP13.continuous.continuousOn ⟨h.1.le, h.2.le⟩
  choose r hr he using h
  refine ⟨r, ?_, hr, he⟩
  intro i j hij
  exact (hr i).2.trans_lt ((saddleRoot_intervals_disjoint i j hij).trans_le (hr j).1)

lemma saddleP13_factor (r : Fin 5 → ℝ) (hr : Function.Injective r)
    (hz : ∀ i, saddleP13.eval (r i) = 0) :
    ∃ b c : ℝ,
      saddleP13 = (∏ i, (X - C (r i))) * (X^2 + C b * X + C c) ∧
      b = (∑ i, r i) - 3872772/156 ∧
      (∏ i, r i) * c = 1758025644874743176035740/156 := by
  classical
  let p : ℝ[X] := ∏ i, (X - C (r i))
  have hp : p.Monic := monic_prod_X_sub_C _ _
  have hpd : p.natDegree = 5 := by
    simp [p, natDegree_finsetProd_X_sub_C_eq_card]
  have hdvd : p ∣ saddleP13 := Fintype.prod_dvd_of_coprime
    (pairwise_coprime_X_sub_C hr) (fun i => (dvd_iff_isRoot).mpr (hz i))
  obtain ⟨g, hg⟩ := hdvd
  have hgm : g.Monic := hp.of_mul_monic_left (hg ▸ saddleP13_monic)
  have hgd : g.natDegree = 2 := by
    have hh := hp.natDegree_mul hgm
    rw [← hg, saddleP13_natDegree, hpd] at hh
    omega
  have hgform : g = X^2 + C (g.coeff 1) * X + C (g.coeff 0) := by
    have hh := g.as_sum_range_C_mul_X_pow
    have hc2 : g.coeff 2 = 1 := hgd ▸ hgm.coeff_natDegree
    rw [hgd] at hh
    norm_num [Finset.sum_range_succ, hc2] at hh
    exact hh.trans (by ring)
  refine ⟨g.coeff 1, g.coeff 0, hg.trans (congrArg (p * ·) hgform), ?_, ?_⟩
  · have hh := hp.nextCoeff_mul hgm
    rw [← hg, nextCoeff_of_natDegree_pos (by rw [saddleP13_natDegree]; norm_num),
      saddleP13_natDegree, nextCoeff_of_natDegree_pos (p := g) (by rw [hgd]; norm_num), hgd,
      show p.nextCoeff = -∑ i, r i from prod_X_sub_C_nextCoeff r] at hh
    norm_num [saddleP13] at hh
    linarith
  · have hh := congrArg (fun f : ℝ[X] => f.coeff 0) hg
    norm_num [saddleP13, p, mul_coeff_zero, coeff_zero_prod, Fin.prod_univ_succ] at hh ⊢
    nlinarith only [hh]

end ZudilinZeta
end

-- Component: missions.zudilin.Params13QuadraticBounds
section
set_option autoImplicit false

open Polynomial

namespace ZudilinZeta

private lemma mul_bounds {x y a b c d : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    a*c ≤ x*y ∧ x*y ≤ b*d :=
  ⟨mul_le_mul hx.1 hy.1 hc (ha.trans hx.1),
    mul_le_mul hx.2 hy.2 (hc.trans hy.1) (ha.trans (hx.1.trans hx.2))⟩

lemma saddleP13_quadratic_bounds (r : Fin 5 → ℝ) (b c : ℝ)
    (hr : ∀ i, r i ∈ Set.Icc (saddleRootLo i) (saddleRootHi i))
    (hb : b = (∑ i, r i) - 3872772/156)
    (hc : (∏ i, r i) * c = 1758025644874743176035740/156) :
    (-14009279477660105/1000000000000 ≤ b ∧ b ≤ -14009279477660104/1000000000000) ∧
    (50314272573632/1000000 ≤ c ∧ c ≤ 50314272573633/1000000) := by
  have h0 := hr 0
  have h1 := hr 1
  have h2 := hr 2
  have h3 := hr 3
  have h4 := hr 4
  norm_num [saddleRootLo, saddleRootHi, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four] at h0 h1 h2 h3 h4
  constructor
  · simp [Fin.sum_univ_succ] at hb
    constructor <;> linarith only [hb, h0.1, h0.2, h1.1, h1.2,
      h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]
  · have p0 : 249790860432482171939475/100000000000000000000 ≤ -r 0 ∧
        -r 0 ≤ 249790860432482171939476/100000000000000000000 := by
      constructor <;> linarith only [h0.1, h0.2]
    have p1 : 68538486020573165705125/100000000000000000000 ≤ -r 1 ∧
        -r 1 ≤ 68538486020573165705126/100000000000000000000 := by
      constructor <;> linarith only [h1.1, h1.2]
    have p2 : 21108648548036042162858/100000000000000000000 ≤ -r 2 ∧
        -r 2 ≤ 21108648548036042162859/100000000000000000000 := by
      constructor <;> linarith only [h2.1, h2.2]
    have p3 : 4348103402618084547974/100000000000000000000 ≤ -r 3 ∧
        -r 3 ≤ 4348103402618084547975/100000000000000000000 := by
      constructor <;> linarith only [h3.1, h3.2]
    have pp := mul_bounds (by norm_num) (by norm_num) p0 p1
    have pp := mul_bounds (by norm_num) (by norm_num) pp p2
    have pp := mul_bounds (by norm_num) (by norm_num) pp p3
    have pp := mul_bounds (by norm_num) (by norm_num) pp h4
    have he : -r 0 * -r 1 * -r 2 * -r 3 * r 4 = ∏ i, r i := by
      simp [Fin.prod_univ_succ]
      ring
    rw [he] at pp
    have hp : 223980087220006264014/1000000 ≤ ∏ i, r i ∧
        (∏ i, r i) ≤ 223980087220006264015/1000000 := by
      constructor <;> norm_num at pp ⊢ <;> linarith only [pp.1, pp.2]
    have hpos : 0 < c := by
      by_contra hh
      have := mul_nonpos_of_nonneg_of_nonpos
        (show 0 ≤ ∏ i, r i by linarith only [hp.1]) (le_of_not_gt hh)
      linarith only [this, hc]
    constructor
    · nlinarith only [hc, mul_le_mul_of_nonneg_right hp.2 hpos.le]
    · nlinarith only [hc, mul_le_mul_of_nonneg_right hp.1 hpos.le]

end ZudilinZeta
end

-- Component: missions.zudilin.Params13SaddleGeometry
section
set_option autoImplicit false

open Polynomial

namespace ZudilinZeta

lemma quadratic_nonreal_coordinates (b c : ℝ) (hd : b^2 < 4*c) (z : ℂ)
    (hz : z^2 + (b : ℂ)*z + (c : ℂ) = 0) :
    z.re = -b/2 ∧ z.re^2 + z.im^2 = c := by
  have hRe := congrArg Complex.re hz
  have hIm := congrArg Complex.im hz
  simp [pow_two, Complex.mul_re, Complex.mul_im] at hRe hIm
  have hne : z.im ≠ 0 := by
    intro he
    rw [he] at hRe
    nlinarith only [hd, hRe, sq_nonneg (2*z.re+b)]
  have hh : (2*z.re+b)*z.im = 0 := by nlinarith only [hIm]
  have hh := (mul_eq_zero.mp hh).resolve_right hne
  constructor
  · linarith only [hh]
  · have hb : b = -2*z.re := by linarith only [hh]
    rw [hb] at hRe
    nlinarith only [hRe]

lemma saddleP13_quartic_coordinates (b c : ℝ)
    (hb : -14009279477660105/1000000000000 ≤ b ∧ b ≤ -14009279477660104/1000000000000)
    (hc : 50314272573632/1000000 ≤ c ∧ c ≤ 50314272573633/1000000) :
    ∃ u v : ℝ, 0 < u ∧ 0 < v ∧
      u^2-v^2 = -b/2 ∧ (u^2+v^2)^2 = c ∧
      (87479005418345/1000000000000 ≤ (u+91)/2 ∧
        (u+91)/2 ≤ 87479005418346/1000000000000) ∧
      (3328206905525/1000000000000 ≤ v/2 ∧
        v/2 ≤ 3328206905527/1000000000000) := by
  let s := Real.sqrt c
  have hs0 : 0 ≤ s := Real.sqrt_nonneg c
  have hs2 : s^2 = c := Real.sq_sqrt (by linarith only [hc.1])
  have hs : 709325542847795/100000000000 ≤ s ∧
      s ≤ 709325542847803/100000000000 := by
    constructor
    · nlinarith only [hs0, hs2, hc.1]
    · nlinarith only [hs0, hs2, hc.2]
  let u := Real.sqrt ((s-b/2)/2)
  let v := Real.sqrt ((s+b/2)/2)
  have hu0 : 0 < u := Real.sqrt_pos.mpr (by linarith only [hs.1, hb.2])
  have hv0 : 0 < v := Real.sqrt_pos.mpr (by linarith only [hs.1, hb.1])
  have hu2 : u^2 = (s-b/2)/2 := Real.sq_sqrt (by linarith only [hs.1, hb.2])
  have hv2 : v^2 = (s+b/2)/2 := Real.sq_sqrt (by linarith only [hs.1, hb.1])
  refine ⟨u, v, hu0, hv0, ?_, ?_, ?_, ?_⟩
  · linarith only [hu2, hv2]
  · rw [show u^2+v^2=s by linarith only [hu2, hv2], hs2]
  · constructor
    · nlinarith only [hu0, hu2, hs.1, hb.2]
    · nlinarith only [hu0, hu2, hs.2, hb.1]
  · constructor
    · nlinarith only [hv0, hv2, hs.1, hb.1]
    · nlinarith only [hv0, hv2, hs.2, hb.2]

lemma quartic_root_of_coordinates (b c u v : ℝ)
    (huv : u^2-v^2 = -b/2) (hc : (u^2+v^2)^2=c) :
    (((u : ℂ)+(v : ℂ)*Complex.I)^2)^2 +
      (b : ℂ)*((u : ℂ)+(v : ℂ)*Complex.I)^2 + (c : ℂ) = 0 := by
  have hb : b = -2*(u^2-v^2) := by linarith only [huv]
  rw [hb, ← hc]
  push_cast
  ring_nf
  norm_num [Complex.I_sq, pow_succ]
  ring

lemma quartic_root_re_le (b c u v : ℝ) (hu : 0 < u) (hv : 0 < v)
    (huv : u^2-v^2 = -b/2) (hc : (u^2+v^2)^2=c)
    (z : ℂ) (hz : (z^2)^2 + (b : ℂ)*z^2 + (c : ℂ)=0) : z.re ≤ u := by
  have hd : b^2 < 4*c := by
    have hh := mul_pos (sq_pos_of_pos hu) (sq_pos_of_pos hv)
    rw [show b = -2*(u^2-v^2) by linarith only [huv], ← hc]
    nlinarith only [hh]
  obtain ⟨hr, hn⟩ := quadratic_nonreal_coordinates b c hd (z^2) hz
  simp [pow_two, Complex.mul_re, Complex.mul_im] at hr hn
  have hn' : (z.re^2+z.im^2)^2=(u^2+v^2)^2 := by nlinarith only [hn, hc]
  have he : z.re^2+z.im^2=u^2+v^2 :=
    (sq_eq_sq₀ (by positivity) (by positivity)).mp hn'
  nlinarith only [hr, huv, he, hu]

lemma saddleP13_factor_complex (r : Fin 5 → ℝ) (b c : ℝ)
    (hf : saddleP13 = (∏ i, (X-C (r i))) * (X^2+C b*X+C c)) (z : ℂ) :
    saddleQ13 z = 156*(∏ i, (z-(r i : ℂ)))*(z^2+(b : ℂ)*z+(c : ℂ)) := by
  rw [← saddleP13_complex, hf]
  simp [map_prod]
  ring

lemma saddle_root_params13_geometry :
    ∃ τ₀ : ℂ, charPoly params13 τ₀=0 ∧ 0<τ₀.im ∧
      (∀ τ : ℂ, charPoly params13 τ=0 → 0<τ.im → τ.re≤τ₀.re) ∧
      (87479005418345/1000000000000 ≤ τ₀.re ∧
        τ₀.re ≤ 87479005418346/1000000000000) ∧
      (3328206905525/1000000000000 ≤ τ₀.im ∧
        τ₀.im ≤ 3328206905527/1000000000000) := by
  obtain ⟨r, hmono, hbounds, hroots⟩ := saddleP13_real_roots
  obtain ⟨b, c, hfactor, hb, hc⟩ := saddleP13_factor r hmono.injective hroots
  obtain ⟨hb', hc'⟩ := saddleP13_quadratic_bounds r b c hbounds hb hc
  obtain ⟨u, v, hu, hv, huv, hc2, hure, hvim⟩ := saddleP13_quartic_coordinates b c hb' hc'
  let w : ℂ := (u : ℂ)+(v : ℂ)*Complex.I
  let τ₀ : ℂ := (w+91)/2
  have hwre : w.re=u := by simp [w]
  have hwim : w.im=v := by simp [w]
  have hτre : τ₀.re=(u+91)/2 := by simp [τ₀, hwre]
  have hτim : τ₀.im=v/2 := by simp [τ₀, hwim]
  have hw : 2*τ₀-91=w := by dsimp only [τ₀]; ring
  have hwroot : saddleQ13 (w^2)=0 := by
    rw [saddleP13_factor_complex r b c hfactor,
      quartic_root_of_coordinates b c u v huv hc2, mul_zero]
  refine ⟨τ₀, ?_, by rw [hτim]; positivity, ?_, hτre.symm ▸ hure, hτim.symm ▸ hvim⟩
  · have hh := charPoly_params13_reduction τ₀
    rw [hw, hwroot, mul_zero] at hh
    exact (mul_eq_zero.mp hh).resolve_left (by norm_num)
  · intro τ hτ hτi
    let z : ℂ := 2*τ-91
    have hzre : z.re=2*τ.re-91 := by simp [z]
    have hzim : z.im=2*τ.im := by simp [z]
    have hzpos : 0<z.im := by rw [hzim]; positivity
    have hz0 : z≠0 := by
      intro he
      rw [he, Complex.zero_im] at hzpos
      exact lt_irrefl _ hzpos
    have hq : saddleQ13 (z^2)=0 := by
      have hh := charPoly_params13_reduction τ
      rw [hτ, mul_zero] at hh
      exact (mul_eq_zero.mp hh.symm).resolve_left hz0
    rw [saddleP13_factor_complex r b c hfactor] at hq
    rcases mul_eq_zero.mp hq with hq | hq
    · have hp : (∏ i, (z^2-(r i : ℂ)))=0 :=
        (mul_eq_zero.mp hq).resolve_left (by norm_num)
      obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hp
      have hi := congrArg Complex.im (sub_eq_zero.mp hi)
      simp [pow_two, Complex.mul_im] at hi
      have hzre0 : z.re=0 := by nlinarith only [hi, hzpos]
      rw [hτre]
      linarith only [hzre, hzre0, hu]
    · have hh := quartic_root_re_le b c u v hu hv huv hc2 z hq
      rw [hτre]
      linarith only [hzre, hh]

end ZudilinZeta
end

-- Component: missions.zudilin.Params13SaddleUniqueness
section
set_option autoImplicit false

open Polynomial

namespace ZudilinZeta

lemma saddle_params13_right_root_unique (τ σ : ℂ)
    (hτ : charPoly params13 τ=0) (hσ : charPoly params13 σ=0)
    (hτi : 0<τ.im) (hσi : 0<σ.im) (hτr : 91/2<τ.re) (hre : τ.re=σ.re) : τ=σ := by
  obtain ⟨r, hmono, hbounds, hroots⟩ := saddleP13_real_roots
  obtain ⟨b, c, hfactor, hb, hc⟩ := saddleP13_factor r hmono.injective hroots
  obtain ⟨hb', hc'⟩ := saddleP13_quadratic_bounds r b c hbounds hb hc
  have hd : b^2<4*c := by
    have hh := mul_nonneg (show 0≤b+14010 by linarith only [hb'.1])
      (show 0≤14010-b by linarith only [hb'.2])
    nlinarith only [hh, hc'.1]
  have hquad (z : ℂ) (hz : charPoly params13 z=0) (hzi : 0<z.im)
      (hzr : 91/2<z.re) : ((2*z-91)^2)^2+(b : ℂ)*(2*z-91)^2+(c : ℂ)=0 := by
    have hi : 0<(2*z-91).im := by norm_num; linarith only [hzi]
    have hr : 0<(2*z-91).re := by norm_num; linarith only [hzr]
    have hn : 2*z-91≠0 := by
      intro he
      rw [he, Complex.zero_im] at hi
      exact lt_irrefl _ hi
    have hh := charPoly_params13_reduction z
    rw [hz, mul_zero] at hh
    have hq := (mul_eq_zero.mp hh.symm).resolve_left hn
    rw [saddleP13_factor_complex r b c hfactor] at hq
    rcases mul_eq_zero.mp hq with hq | hq
    · have hp : (∏ i, ((2*z-91)^2-(r i : ℂ)))=0 :=
        (mul_eq_zero.mp hq).resolve_left (by norm_num)
      obtain ⟨i, _, he⟩ := Finset.prod_eq_zero_iff.mp hp
      have he := congrArg Complex.im (sub_eq_zero.mp he)
      simp only [pow_two, Complex.mul_im, Complex.ofReal_im] at he
      nlinarith only [he, mul_pos hr hi]
    · exact hq
  have ha := (quadratic_nonreal_coordinates b c hd ((2*τ-91)^2)
    (hquad τ hτ hτi hτr)).1
  have hs := (quadratic_nonreal_coordinates b c hd ((2*σ-91)^2)
    (hquad σ hσ hσi (by simpa only [← hre] using hτr))).1
  norm_num [pow_two, Complex.mul_re, Complex.mul_im] at ha hs
  rw [← hre] at hs
  have himsq : τ.im^2=σ.im^2 := by nlinarith only [ha, hs]
  exact Complex.ext hre ((sq_eq_sq₀ hτi.le hσi.le).mp himsq)

lemma saddle_params13_maximal_root_box (τ : ℂ) (hτ : charPoly params13 τ=0)
    (hτi : 0<τ.im)
    (hmax : ∀ σ : ℂ, charPoly params13 σ=0 → 0<σ.im → σ.re≤τ.re) :
    (87479005418345/1000000000000 ≤ τ.re ∧
      τ.re ≤ 87479005418346/1000000000000) ∧
    (3328206905525/1000000000000 ≤ τ.im ∧
      τ.im ≤ 3328206905527/1000000000000) := by
  obtain ⟨σ, hσ, hσi, hσmax, hx, hy⟩ := saddle_root_params13_geometry
  have hre : τ.re=σ.re := le_antisymm (hσmax τ hτ hτi) (hmax σ hσ hσi)
  have he := saddle_params13_right_root_unique τ σ hτ hσ hτi hσi
    (by rw [hre]; linarith only [hx.1]) hre
  simpa only [he] using And.intro hx hy

end ZudilinZeta
end

-- Component: missions.zudilin.Params13SaddleStationarity
section
set_option autoImplicit false

namespace ZudilinZeta

lemma saddlePhaseDeriv_params13_im_formula (τ : ℂ)
    (hx : 87≤τ.re ∧ τ.re≤175/2) :
    (saddlePhaseDeriv params13 τ).im=
      3*(Real.arctan (τ.im/τ.re)+Real.arctan (τ.im/(91-τ.re)))+
      3*(Real.arctan (τ.im/(τ.re-64))-Real.arctan (τ.im/(τ.re-27)))+
      ∑ j∈Finset.Icc (29 : ℕ) 38,
        (Real.arctan (τ.im/(τ.re-91+j))-Real.arctan (τ.im/(τ.re-j))) := by
  norm_num [saddlePhaseDeriv, params13, eta13, Finset.sum_Icc_succ_top,
    Complex.mul_im, Complex.log_im]
  repeat' rw [arg_eq_arctan_of_re_pos _ (by norm_num; linarith only [hx.1, hx.2])]
  norm_num [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    neg_div, Real.arctan_neg]
  ring

private lemma arctan_small_ratio (y a : ℝ) (hy : 0≤y) (hyu : y≤7/2) (ha : 20≤a) :
    0≤Real.arctan (y/a) ∧ Real.arctan (y/a)≤1/5 := by
  have ha' : 0<a := by linarith only [ha]
  have hratio : 0≤y/a ∧ y/a≤1/5 := by
    refine ⟨div_nonneg hy ha'.le, (div_le_iff₀ ha').mpr ?_⟩
    linarith only [ha, hyu]
  exact arctan_rational_enclosure (y/a) 0 (1/5) 0 (1/5) (by norm_num)
    hratio (by norm_num) (by norm_num)

private lemma arctan_eta_difference (x y e : ℝ)
    (hx : 87≤x) (hy : 0≤y) (hyu : y≤7/2) (he : 27≤e ∧ e≤38) :
    0≤Real.arctan (y/(x-91+e))-Real.arctan (y/(x-e)) ∧
      Real.arctan (y/(x-91+e))-Real.arctan (y/(x-e))≤1/5 := by
  have ha : 20≤x-91+e := by linarith only [hx, he.1]
  have hb : 20≤x-e := by linarith only [hx, he.2]
  have ha' : 0<x-91+e := by linarith only [ha]
  have hab : x-91+e≤x-e := by linarith only [he.2]
  have hratio := div_le_div_of_nonneg_left hy ha' hab
  have hmono := Real.arctan_le_arctan_iff.mpr hratio
  have hupper := (arctan_small_ratio y (x-91+e) hy hyu ha).2
  have hlower := (arctan_small_ratio y (x-e) hy hyu hb).1
  constructor <;> linarith only [hmono, hupper, hlower]

lemma saddlePhaseDeriv_params13_im_bounds (τ : ℂ)
    (hx : 87≤τ.re ∧ τ.re≤175/2) (hy : 0<τ.im ∧ τ.im≤7/2) :
    0<(saddlePhaseDeriv params13 τ).im ∧
      (saddlePhaseDeriv params13 τ).im<2*Real.pi := by
  rw [saddlePhaseDeriv_params13_im_formula τ hx]
  have ht := arctan_small_ratio τ.im τ.re hy.1.le hy.2 (by linarith only [hx.1])
  have hd : 0<Real.arctan (τ.im/(91-τ.re)) ∧
      Real.arctan (τ.im/(91-τ.re))≤Real.pi/4 := by
    have hdpos : 0<91-τ.re := by linarith only [hx.2]
    refine ⟨Real.arctan_pos.mpr (div_pos hy.1 hdpos), ?_⟩
    rw [← Real.arctan_one]
    apply Real.arctan_le_arctan_iff.mpr
    apply (div_le_iff₀ hdpos).mpr
    linarith only [hx.2, hy.2]
  have h27 := arctan_eta_difference τ.re τ.im 27 hx.1 hy.1.le hy.2 (by norm_num)
  rw [show τ.re-91+27=τ.re-64 by ring] at h27
  have hsumlo : 0≤∑ j∈Finset.Icc (29 : ℕ) 38,
      (Real.arctan (τ.im/(τ.re-91+j))-Real.arctan (τ.im/(τ.re-j))) := by
    apply Finset.sum_nonneg
    intro j hj
    have hjr : (27 : ℝ)≤j ∧ (j : ℝ)≤38 := by
      obtain ⟨hjlo, hjhi⟩ := Finset.mem_Icc.mp hj
      constructor
      · exact_mod_cast (show 27≤j by omega)
      · exact_mod_cast hjhi
    exact (arctan_eta_difference τ.re τ.im (j : ℝ) hx.1 hy.1.le hy.2 hjr).1
  have hsumhi : (∑ j∈Finset.Icc (29 : ℕ) 38,
      (Real.arctan (τ.im/(τ.re-91+j))-Real.arctan (τ.im/(τ.re-j))))≤2 := by
    calc
      _ ≤ ∑ j∈Finset.Icc (29 : ℕ) 38, (1/5 : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjr : (27 : ℝ)≤j ∧ (j : ℝ)≤38 := by
          obtain ⟨hjlo, hjhi⟩ := Finset.mem_Icc.mp hj
          constructor
          · exact_mod_cast (show 27≤j by omega)
          · exact_mod_cast hjhi
        exact (arctan_eta_difference τ.re τ.im (j : ℝ) hx.1 hy.1.le hy.2 hjr).2
      _ = 2 := by norm_num [Finset.sum_const, Nat.card_Icc]
  constructor
  · linarith only [ht.1, hd.1, h27.1, hsumlo]
  · linarith only [ht.2, hd.2, h27.2, hsumhi, Real.pi_gt_three]

lemma saddlePhaseDeriv_params13_eq_pi_mul_I (τ : ℂ)
    (hroot : charPoly params13 τ=0) (him : 0<τ.im)
    (hmax : ∀ σ : ℂ, charPoly params13 σ=0 → 0<σ.im → σ.re≤τ.re) :
    saddlePhaseDeriv params13 τ=Real.pi*Complex.I := by
  obtain ⟨hx, hy⟩ := saddle_params13_maximal_root_box τ hroot him hmax
  obtain ⟨hlo, hhi⟩ := saddlePhaseDeriv_params13_im_bounds τ
    ⟨by linarith only [hx.1], by linarith only [hx.2]⟩
    ⟨him, by linarith only [hy.2]⟩
  have hexp := exp_saddlePhaseDeriv_of_root params13 rfl τ him hroot
  rw [← Complex.exp_pi_mul_I] at hexp
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  have hki := congrArg Complex.im hk
  norm_num [Complex.mul_im] at hki
  have hklo : 0≤k := by
    by_contra hn
    have hn' : (k : ℝ)≤-1 := by exact_mod_cast (show k≤-1 by omega)
    nlinarith only [hki, hlo, hn', Real.pi_pos]
  have hkhi : k≤0 := by
    by_contra hn
    have hn' : (1 : ℝ)≤k := by exact_mod_cast (show 1≤k by omega)
    nlinarith only [hki, hhi, hn', Real.pi_pos]
  have hkzero : k=0 := le_antisymm hkhi hklo
  simpa only [hkzero, Int.cast_zero, zero_mul, add_zero] using hk

lemma saddlePhase_params13_stationary_value (τ : ℂ)
    (hroot : charPoly params13 τ=0) (him : 0<τ.im)
    (hmax : ∀ σ : ℂ, charPoly params13 σ=0 → 0<σ.im → σ.re≤τ.re) :
    saddlePhase params13 τ-τ*(Real.pi*Complex.I)=f0 params13 τ := by
  rw [← saddlePhaseDeriv_params13_eq_pi_mul_I τ hroot him hmax]
  exact saddlePhase_sub_mul_deriv params13 τ

end ZudilinZeta
end

-- Component: missions.zudilin.SaddleCurvature
section
set_option autoImplicit false

namespace ZudilinZeta

noncomputable def saddlePhaseSecond (P : Params) (τ : ℂ) : ℂ :=
  (P.r : ℂ)*(τ⁻¹+((P.eta 0 : ℂ)-τ)⁻¹)+
  ∑ j∈Finset.Icc 1 P.q,
    ((τ-(P.eta 0 : ℂ)+(P.eta j : ℂ))⁻¹-(τ-(P.eta j : ℂ))⁻¹)

lemma hasDerivAt_saddlePhaseDeriv (P : Params) (τ : ℂ)
    (hτ : τ∈Complex.slitPlane)
    (h0 : (P.eta 0 : ℂ)-τ∈Complex.slitPlane)
    (hplus : ∀ j∈Finset.Icc 1 P.q,
      τ-(P.eta 0 : ℂ)+(P.eta j : ℂ)∈Complex.slitPlane)
    (hminus : ∀ j∈Finset.Icc 1 P.q, τ-(P.eta j : ℂ)∈Complex.slitPlane) :
    HasDerivAt (saddlePhaseDeriv P) (saddlePhaseSecond P τ) τ := by
  have hfirst : HasDerivAt
      (fun z : ℂ => (P.r : ℂ)*(Complex.log z-Complex.log ((P.eta 0 : ℂ)-z)))
      ((P.r : ℂ)*(τ⁻¹+((P.eta 0 : ℂ)-τ)⁻¹)) τ := by
    convert! ((Complex.hasDerivAt_log hτ).sub
      (((hasDerivAt_id τ).const_sub (P.eta 0 : ℂ)).clog h0)).const_mul (P.r : ℂ) using 1
    simp only [id_eq, neg_div, one_div, sub_neg_eq_add]
  have hsum : HasDerivAt
      (fun z : ℂ => ∑ j∈Finset.Icc 1 P.q,
        (Complex.log (z-(P.eta 0 : ℂ)+(P.eta j : ℂ))-Complex.log (z-(P.eta j : ℂ))))
      (∑ j∈Finset.Icc 1 P.q,
        ((τ-(P.eta 0 : ℂ)+(P.eta j : ℂ))⁻¹-(τ-(P.eta j : ℂ))⁻¹)) τ := by
    apply HasDerivAt.fun_sum
    intro j hj
    convert! ((((hasDerivAt_id τ).sub_const (P.eta 0 : ℂ)).add_const
      (P.eta j : ℂ)).clog (hplus j hj)).sub
      (((hasDerivAt_id τ).sub_const (P.eta j : ℂ)).clog (hminus j hj)) using 1
    simp only [id_eq, one_div]
  exact hfirst.add hsum

lemma saddle_log_arguments_mem_slitPlane (P : Params) (τ : ℂ) (him : 0<τ.im) :
    τ∈Complex.slitPlane ∧ (P.eta 0 : ℂ)-τ∈Complex.slitPlane ∧
      (∀ j∈Finset.Icc 1 P.q, τ-(P.eta 0 : ℂ)+(P.eta j : ℂ)∈Complex.slitPlane) ∧
      (∀ j∈Finset.Icc 1 P.q, τ-(P.eta j : ℂ)∈Complex.slitPlane) := by
  refine ⟨Complex.mem_slitPlane_iff.mpr (Or.inr him.ne'), ?_, ?_, ?_⟩
  · apply Complex.mem_slitPlane_iff.mpr
    right
    simpa only [Complex.sub_im, Complex.natCast_im, zero_sub, neg_ne_zero] using him.ne'
  · intro j hj
    apply Complex.mem_slitPlane_iff.mpr
    right
    simpa only [Complex.add_im, Complex.sub_im, Complex.natCast_im, sub_zero, add_zero] using him.ne'
  · intro j hj
    apply Complex.mem_slitPlane_iff.mpr
    right
    simpa only [Complex.sub_im, Complex.natCast_im, sub_zero] using him.ne'

lemma hasDerivAt_saddlePhase_of_im_pos (P : Params) (τ : ℂ) (him : 0<τ.im) :
    HasDerivAt (saddlePhase P) (saddlePhaseDeriv P τ) τ := by
  obtain ⟨ht, h0, hp, hm⟩ := saddle_log_arguments_mem_slitPlane P τ him
  exact hasDerivAt_saddlePhase P τ ht h0 hp hm

lemma hasDerivAt_saddlePhaseDeriv_of_im_pos (P : Params) (τ : ℂ) (him : 0<τ.im) :
    HasDerivAt (saddlePhaseDeriv P) (saddlePhaseSecond P τ) τ := by
  obtain ⟨ht, h0, hp, hm⟩ := saddle_log_arguments_mem_slitPlane P τ him
  exact hasDerivAt_saddlePhaseDeriv P τ ht h0 hp hm

private lemma real_inverse_quadratic_difference_nonneg (a b y : ℝ)
    (ha : 0<a) (hab : a≤b) (hy : y^2≤a*b) :
    0≤a/(a^2+y^2)-b/(b^2+y^2) := by
  have hb : 0<b := ha.trans_le hab
  have had : 0<a^2+y^2 := by positivity
  have hbd : 0<b^2+y^2 := by positivity
  rw [sub_nonneg, div_le_div_iff₀ hbd had]
  have hh := mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hy)
  nlinarith only [hh]

lemma saddle_reciprocal_difference_re_nonneg (τ : ℂ) (e : ℝ)
    (hx : 87≤τ.re) (hy : |τ.im|≤10) (he : 27≤e ∧ e≤38) :
    0≤((τ-91+(e : ℂ))⁻¹-(τ-(e : ℂ))⁻¹).re := by
  have ha : 23≤τ.re-91+e := by linarith only [hx, he.1]
  have hb : 49≤τ.re-e := by linarith only [hx, he.2]
  have ha' : 0<τ.re-91+e := by linarith only [ha]
  have hab : τ.re-91+e≤τ.re-e := by linarith only [he.2]
  have hprod : 23*49≤(τ.re-91+e)*(τ.re-e) :=
    mul_le_mul ha hb (by norm_num) (by linarith only [ha])
  have hy' := (sq_le_sq₀ (abs_nonneg τ.im) (by norm_num : (0 : ℝ)≤10)).mpr hy
  rw [sq_abs] at hy'
  have hh := real_inverse_quadratic_difference_nonneg (τ.re-91+e) (τ.re-e) τ.im
    ha' hab (by linarith only [hprod, hy'])
  simpa only [Complex.sub_re, Complex.add_re, Complex.inv_re, Complex.normSq_apply,
    Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_im, Complex.add_im, sub_zero, add_zero, ← pow_two] using hh

private lemma inverse_re_pos (z : ℂ) (hz : 0<z.re) : 0<(z⁻¹).re := by
  rw [Complex.inv_re]
  apply div_pos hz
  apply Complex.normSq_pos.mpr
  intro he
  simpa [he] using hz

private lemma eta13_between (j : ℕ) (hj : j∈Finset.Icc 1 13) :
    27≤eta13 j ∧ eta13 j≤38 := by
  obtain ⟨hjlo, hjhi⟩ := Finset.mem_Icc.mp hj
  unfold eta13
  split_ifs <;> omega

lemma saddlePhaseSecond_params13_re_pos (τ : ℂ)
    (hx : 87≤τ.re ∧ τ.re≤175/2) (hy : |τ.im|≤10) :
    0<(saddlePhaseSecond params13 τ).re := by
  have ht := inverse_re_pos τ (by linarith only [hx.1])
  have h0 := inverse_re_pos ((91 : ℂ)-τ) (by norm_num; linarith only [hx.2])
  have hs : 0≤∑ j∈Finset.Icc 1 13,
      ((τ-91+(eta13 j : ℂ))⁻¹-(τ-(eta13 j : ℂ))⁻¹).re := by
    apply Finset.sum_nonneg
    intro j hj
    have he : (27 : ℝ)≤eta13 j ∧ (eta13 j : ℝ)≤38 := by
      exact_mod_cast eta13_between j hj
    exact_mod_cast saddle_reciprocal_difference_re_nonneg τ (eta13 j : ℝ) hx.1 hy he
  change 0<((3 : ℂ)*(τ⁻¹+((91 : ℂ)-τ)⁻¹)+
    ∑ j∈Finset.Icc 1 13, ((τ-91+(eta13 j : ℂ))⁻¹-(τ-(eta13 j : ℂ))⁻¹)).re
  simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
    zero_mul, sub_zero, Complex.re_sum]
  linarith only [ht, h0, hs]

end ZudilinZeta
end

-- Component: missions.zudilin.Params13VerticalPhase
section
set_option autoImplicit false

namespace ZudilinZeta

noncomputable def adjustedSaddlePhase (P : Params) (τ : ℂ) : ℂ :=
  saddlePhase P τ-τ*(Real.pi*Complex.I)

private lemma eta13_between_real (j : ℕ) (hj : j∈Finset.Icc 1 13) :
    (27 : ℝ)≤eta13 j ∧ (eta13 j : ℝ)≤38 := by
  have hj' := Finset.mem_Icc.mp hj
  have h : 27≤eta13 j ∧ eta13 j≤38 := by
    unfold eta13
    split_ifs <;> omega
  exact_mod_cast h

lemma params13_log_arguments_mem_slitPlane (τ : ℂ)
    (hx : 87≤τ.re ∧ τ.re≤175/2) :
    τ∈Complex.slitPlane ∧ (params13.eta 0 : ℂ)-τ∈Complex.slitPlane ∧
      (∀ j∈Finset.Icc 1 params13.q,
        τ-(params13.eta 0 : ℂ)+(params13.eta j : ℂ)∈Complex.slitPlane) ∧
      (∀ j∈Finset.Icc 1 params13.q, τ-(params13.eta j : ℂ)∈Complex.slitPlane) := by
  refine ⟨Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith only [hx.1])), ?_, ?_, ?_⟩
  · apply Complex.mem_slitPlane_iff.mpr
    left
    change 0<((91 : ℂ)-τ).re
    norm_num
    linarith only [hx.2]
  · intro j hj
    have he := eta13_between_real j hj
    apply Complex.mem_slitPlane_iff.mpr
    left
    change 0<(τ-91+(eta13 j : ℂ)).re
    simp only [Complex.add_re, Complex.sub_re, Complex.re_ofNat, Complex.natCast_re]
    linarith only [hx.1, he.1]
  · intro j hj
    have he := eta13_between_real j hj
    apply Complex.mem_slitPlane_iff.mpr
    left
    change 0<(τ-(eta13 j : ℂ)).re
    simp only [Complex.sub_re, Complex.natCast_re]
    linarith only [hx.1, he.2]

lemma hasDerivAt_adjustedSaddlePhase_params13 (τ : ℂ)
    (hx : 87≤τ.re ∧ τ.re≤175/2) :
    HasDerivAt (adjustedSaddlePhase params13)
      (saddlePhaseDeriv params13 τ-Real.pi*Complex.I) τ := by
  obtain ⟨ht, h0, hp, hm⟩ := params13_log_arguments_mem_slitPlane τ hx
  convert! (hasDerivAt_saddlePhase params13 τ ht h0 hp hm).sub
    ((hasDerivAt_id τ).mul_const (Real.pi*Complex.I)) using 1
  simp only [one_mul]

lemma hasDerivAt_adjustedSaddlePhase_vertical (x y : ℝ)
    (hx : 87≤x ∧ x≤175/2) :
    HasDerivAt
      (fun t : ℝ => (adjustedSaddlePhase params13 ((x : ℂ)+(t : ℂ)*Complex.I)).re)
      (Real.pi-(saddlePhaseDeriv params13 ((x : ℂ)+(y : ℂ)*Complex.I)).im) y := by
  have hz : 87≤((x : ℂ)+(y : ℂ)*Complex.I).re ∧
      ((x : ℂ)+(y : ℂ)*Complex.I).re≤175/2 := by simpa using hx
  have h := (hasDerivAt_adjustedSaddlePhase_params13 _ hz).comp (y : ℂ)
    (((hasDerivAt_id (y : ℂ)).mul_const Complex.I).const_add (x : ℂ))
  convert! h.real_of_complex using 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    one_mul, mul_one, mul_zero, zero_mul, sub_zero, zero_sub]
  ring

lemma hasDerivAt_saddlePhaseDeriv_im_vertical (x y : ℝ)
    (hx : 87≤x ∧ x≤175/2) :
    HasDerivAt
      (fun t : ℝ => (saddlePhaseDeriv params13 ((x : ℂ)+(t : ℂ)*Complex.I)).im)
      (saddlePhaseSecond params13 ((x : ℂ)+(y : ℂ)*Complex.I)).re y := by
  have hz : 87≤((x : ℂ)+(y : ℂ)*Complex.I).re ∧
      ((x : ℂ)+(y : ℂ)*Complex.I).re≤175/2 := by simpa using hx
  obtain ⟨ht, h0, hp, hm⟩ := params13_log_arguments_mem_slitPlane _ hz
  have h := (hasDerivAt_saddlePhaseDeriv params13 _ ht h0 hp hm).comp (y : ℂ)
    (((hasDerivAt_id (y : ℂ)).mul_const Complex.I).const_add (x : ℂ))
  convert! (h.mul_const (-Complex.I)).real_of_complex using 1 <;>
    simp only [Function.comp_apply, id_eq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.I_re, Complex.I_im, one_mul, mul_one, mul_neg_one,
      mul_zero, zero_mul, sub_zero, zero_sub, add_zero, neg_zero, neg_neg]

lemma strictMonoOn_saddlePhaseDeriv_im_vertical (x : ℝ)
    (hx : 87≤x ∧ x≤175/2) :
    StrictMonoOn
      (fun y : ℝ => (saddlePhaseDeriv params13 ((x : ℂ)+(y : ℂ)*Complex.I)).im)
      (Set.Icc (-10) 10) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc (-10 : ℝ) 10)
    (fun y hy => (hasDerivAt_saddlePhaseDeriv_im_vertical x y hx).continuousAt.continuousWithinAt)
    (fun y hy => (hasDerivAt_saddlePhaseDeriv_im_vertical x y hx).hasDerivWithinAt)
  intro y hy
  have hy' := interior_subset hy
  have hya : |y|≤10 := abs_le.mpr ⟨hy'.1, hy'.2⟩
  apply saddlePhaseSecond_params13_re_pos
  · simpa using hx
  · simpa using hya

lemma adjustedSaddlePhase_params13_saddle_derivative (τ : ℂ)
    (hroot : charPoly params13 τ=0) (him : 0<τ.im)
    (hmax : ∀ σ : ℂ, charPoly params13 σ=0 → 0<σ.im → σ.re≤τ.re) :
    HasDerivAt (adjustedSaddlePhase params13) 0 τ := by
  obtain ⟨hx, hy⟩ := saddle_params13_maximal_root_box τ hroot him hmax
  have h := hasDerivAt_adjustedSaddlePhase_params13 τ
    ⟨by linarith only [hx.1], by linarith only [hx.2]⟩
  simpa only [saddlePhaseDeriv_params13_eq_pi_mul_I τ hroot him hmax, sub_self] using h

lemma saddle_gaussian_integral_nonzero (τ : ℂ)
    (hroot : charPoly params13 τ=0) (him : 0<τ.im)
    (hmax : ∀ σ : ℂ, charPoly params13 σ=0 → 0<σ.im → σ.re≤τ.re) :
    (∫ t : ℝ, Complex.exp (-(saddlePhaseSecond params13 τ/2)*(t : ℂ)^2))≠0 := by
  obtain ⟨hx, hy⟩ := saddle_params13_maximal_root_box τ hroot him hmax
  have hs := saddlePhaseSecond_params13_re_pos τ
    ⟨by linarith only [hx.1], by linarith only [hx.2]⟩
    (by rw [abs_of_pos him]; linarith only [hy.2])
  have hb : 0<(saddlePhaseSecond params13 τ/2).re := by
    simpa using (half_pos hs)
  rw [integral_gaussian_complex hb]
  apply Complex.cpow_ne_zero_iff.mpr
  left
  apply div_ne_zero
  · exact_mod_cast Real.pi_ne_zero
  · intro he
    simpa [he] using hb

end ZudilinZeta
end

-- Component: missions.zudilin.SaddleGaussianScaling
section
set_option autoImplicit false
noncomputable section
open Complex Filter Topology Set

namespace ZudilinZeta

lemma quadratic_taylor_remainder {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hder : deriv f 0 = 0) :
    Tendsto (fun t : ℝ =>
      (f t - f 0 - ((deriv (deriv f) 0) / 2) * (t : ℂ) ^ 2) / (t : ℂ) ^ 2)
      (𝓝 0) (𝓝 0) := by
  have ht := taylor_tendsto (f := f) (x₀ := 0) (n := 2) convex_univ (mem_univ 0) hf.contDiffOn
  have heval (t : ℝ) : taylorWithinEval f 2 univ 0 t =
      f 0 + (deriv (deriv f) 0 / 2) * (t : ℂ) ^ 2 := by
    rw [taylor_within_apply]
    norm_num [Finset.sum_range_succ, taylorCoeffWithin, iteratedDerivWithin_univ,
      iteratedDeriv_succ, iteratedDeriv_zero, hder, Complex.real_smul]
    ring
  simp only [nhdsWithin_univ, sub_zero, heval] at ht
  convert! ht using 1
  ext t
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow]
  ring

lemma tendsto_saddle_scaled_phase {f : ℝ → ℂ} {b : ℂ}
    (hf : Tendsto (fun t : ℝ =>
      (f t - f 0 - b * (t : ℂ) ^ 2) / (t : ℂ) ^ 2) (𝓝 0) (𝓝 0)) (u : ℝ) :
    Tendsto (fun n : ℕ => (n : ℂ) *
      (f (u / Real.sqrt (n : ℝ)) - f 0)) atTop (𝓝 (b * (u : ℂ) ^ 2)) := by
  by_cases hu : u = 0
  · simpa [hu] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
  have hs : Tendsto (fun n : ℕ => u / Real.sqrt (n : ℝ)) atTop (𝓝 0) :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_div_atTop u
  have h := ((hf.comp hs).add_const b).mul_const ((u : ℂ) ^ 2)
  simp only [zero_add] at h
  apply Tendsto.congr' _ h
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hspos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have harg : ((u / Real.sqrt (n : ℝ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (div_ne_zero hu (ne_of_gt hspos))
  have hscale : (n : ℂ) * (((u / Real.sqrt (n : ℝ) : ℝ) : ℂ) ^ 2) = (u : ℂ) ^ 2 := by
    have hr : (n : ℝ) * (u / Real.sqrt (n : ℝ)) ^ 2 = u ^ 2 := by
      rw [div_pow, Real.sq_sqrt hnpos.le]
      field_simp
    exact_mod_cast hr
  dsimp only [Function.comp_apply]
  rw [← hscale]
  field_simp
  ring

lemma tendsto_saddle_scaled_exponential {f : ℝ → ℂ} {b : ℂ}
    (hf : Tendsto (fun t : ℝ =>
      (f t - f 0 - b * (t : ℂ) ^ 2) / (t : ℂ) ^ 2) (𝓝 0) (𝓝 0)) (u : ℝ) :
    Tendsto (fun n : ℕ => Complex.exp ((n : ℂ) *
      (f (u / Real.sqrt (n : ℝ)) - f 0))) atTop
      (𝓝 (Complex.exp (b * (u : ℂ) ^ 2))) := by
  exact (Complex.continuous_exp.tendsto _).comp (tendsto_saddle_scaled_phase hf u)

end ZudilinZeta
end
end

-- Component: missions.zudilin.SaddleQuadraticDecay
section
set_option autoImplicit false
noncomputable section
open Complex Filter Topology

namespace ZudilinZeta

lemma exists_local_quadratic_decay {f : ℝ → ℂ} {b : ℂ} (hb : b.re < 0)
    (hf : Tendsto (fun t : ℝ =>
      (f t - f 0 - b * (t : ℂ) ^ 2) / (t : ℂ) ^ 2) (𝓝 0) (𝓝 0)) :
    ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧
      ∀ t : ℝ, |t| ≤ δ → (f t - f 0).re ≤ -c * t ^ 2 := by
  let e : ℝ → ℂ := fun t => (f t - f 0 - b * (t : ℂ) ^ 2) / (t : ℂ) ^ 2
  have hc : 0 < -b.re / 2 := by linarith
  have hnorm : ∀ᶠ t : ℝ in 𝓝 0, ‖e t‖ < -b.re / 2 := by
    have h : Tendsto (fun t => ‖e t‖) (𝓝 0) (𝓝 0) := by simpa only [norm_zero] using hf.norm
    exact h.eventually (gt_mem_nhds hc)
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp hnorm
  refine ⟨ε / 2, -b.re / 2, by positivity, hc, ?_⟩
  intro t ht
  by_cases ht0 : t = 0
  · simp [ht0]
  have het : ‖e t‖ < -b.re / 2 := he (by
    rw [Real.dist_eq, sub_zero]
    linarith)
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0
  have hident : f t - f 0 = (e t + b) * (t : ℂ) ^ 2 := by
    dsimp [e]
    field_simp
    ring
  have hre := congrArg Complex.re hident
  simp only [Complex.mul_re, Complex.add_re, ← Complex.ofReal_pow,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at hre
  rw [hre]
  have hh := Complex.re_le_norm (e t)
  have hc' : (e t).re + b.re ≤ -(-b.re / 2) := by linarith
  exact mul_le_mul_of_nonneg_right hc' (sq_nonneg t)

end ZudilinZeta
end
end

-- Component: missions.zudilin.Params13SaddleTaylor
section
set_option autoImplicit false
noncomputable section
open Complex Filter Topology Set

namespace ZudilinZeta

def centeredSaddlePhase (τ : ℂ) (t : ℝ) : ℂ :=
  adjustedSaddlePhase params13 (τ + (t : ℂ) * Complex.I)

lemma analyticAt_adjustedSaddlePhase_strip {w : ℂ} (hw : 87 < w.re ∧ w.re < 175 / 2) :
    AnalyticAt ℂ (adjustedSaddlePhase params13) w := by
  have hopen : IsOpen {z : ℂ | 87 < z.re ∧ z.re < 175 / 2} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  apply DifferentiableOn.analyticAt (s := {z : ℂ | 87 < z.re ∧ z.re < 175 / 2})
    (fun z hz => (hasDerivAt_adjustedSaddlePhase_params13 z
      ⟨hz.1.le, hz.2.le⟩).differentiableAt.differentiableWithinAt) (hopen.mem_nhds hw)

lemma contDiff_centeredSaddlePhase {τ : ℂ} (hx : 87 < τ.re ∧ τ.re < 175 / 2) :
    ContDiff ℝ 2 (centeredSaddlePhase τ) := by
  unfold centeredSaddlePhase
  rw [contDiff_iff_contDiffAt]
  intro t
  have h := analyticAt_adjustedSaddlePhase_strip (w := τ + (t : ℂ) * I) (by simpa using hx)
  have houter : ContDiffAt ℝ 2 (adjustedSaddlePhase params13) (τ + (t : ℂ) * I) :=
    h.contDiffAt.restrict_scalars ℝ
  have hinner : ContDiffAt ℝ 2 (fun t : ℝ => τ + (t : ℂ) * I) t := by
    have hc : ContDiffAt ℝ 2 Complex.ofReal t := Complex.ofRealCLM.contDiff.contDiffAt
    exact contDiffAt_const.add (hc.mul contDiffAt_const)
  convert! houter.comp t hinner using 1

lemma hasDerivAt_centeredSaddlePhase {τ : ℂ} (hx : 87 ≤ τ.re ∧ τ.re ≤ 175 / 2) (t : ℝ) :
    HasDerivAt (centeredSaddlePhase τ)
      ((saddlePhaseDeriv params13 (τ + (t : ℂ) * I) - Real.pi * I) * I) t := by
  have h := (hasDerivAt_adjustedSaddlePhase_params13 (τ + (t : ℂ) * I)
    (by simpa using hx)).comp (t : ℂ) (((hasDerivAt_id (t : ℂ)).mul_const I).const_add τ)
  convert! h.comp_ofReal using 1 <;> simp only [one_mul]

lemma deriv_centeredSaddlePhase_zero (τ : ℂ)
    (hroot : charPoly params13 τ = 0) (him : 0 < τ.im)
    (hmax : ∀ σ : ℂ, charPoly params13 σ = 0 → 0 < σ.im → σ.re ≤ τ.re) :
    deriv (centeredSaddlePhase τ) 0 = 0 := by
  obtain ⟨hx, hy⟩ := saddle_params13_maximal_root_box τ hroot him hmax
  have h := (hasDerivAt_centeredSaddlePhase
    ⟨by linarith only [hx.1], by linarith only [hx.2]⟩ 0).deriv
  simpa only [Complex.ofReal_zero, zero_mul, add_zero,
    saddlePhaseDeriv_params13_eq_pi_mul_I τ hroot him hmax, sub_self, zero_mul] using h

lemma second_deriv_centeredSaddlePhase {τ : ℂ} (hx : 87 ≤ τ.re ∧ τ.re ≤ 175 / 2) :
    deriv (deriv (centeredSaddlePhase τ)) 0 = -saddlePhaseSecond params13 τ := by
  have hf : deriv (centeredSaddlePhase τ) = fun t : ℝ =>
      (saddlePhaseDeriv params13 (τ + (t : ℂ) * I) - Real.pi * I) * I :=
    funext fun t => (hasDerivAt_centeredSaddlePhase hx t).deriv
  rw [hf]
  obtain ⟨ht, h0, hp, hm⟩ := params13_log_arguments_mem_slitPlane τ hx
  have hs : HasDerivAt (saddlePhaseDeriv params13) (saddlePhaseSecond params13 τ)
      (τ + (0 : ℂ) * I) := by
    simpa using hasDerivAt_saddlePhaseDeriv params13 τ ht h0 hp hm
  have hc := hs.comp (0 : ℂ) (((hasDerivAt_id (0 : ℂ)).mul_const I).const_add τ)
  have h := ((hc.sub_const (Real.pi * I)).mul_const I).comp_ofReal
  convert! h.deriv using 1 <;> simp [mul_assoc, Complex.I_sq]

lemma centeredSaddlePhase_taylor (τ : ℂ)
    (hroot : charPoly params13 τ = 0) (him : 0 < τ.im)
    (hmax : ∀ σ : ℂ, charPoly params13 σ = 0 → 0 < σ.im → σ.re ≤ τ.re) :
    Tendsto (fun t : ℝ => (centeredSaddlePhase τ t - centeredSaddlePhase τ 0 -
      (-saddlePhaseSecond params13 τ / 2) * (t : ℂ) ^ 2) / (t : ℂ) ^ 2) (𝓝 0) (𝓝 0) := by
  obtain ⟨hx, hy⟩ := saddle_params13_maximal_root_box τ hroot him hmax
  have hx' : 87 < τ.re ∧ τ.re < 175 / 2 :=
    ⟨by linarith only [hx.1], by linarith only [hx.2]⟩
  have h := quadratic_taylor_remainder (contDiff_centeredSaddlePhase hx')
    (deriv_centeredSaddlePhase_zero τ hroot him hmax)
  simpa only [second_deriv_centeredSaddlePhase ⟨hx'.1.le, hx'.2.le⟩] using h

lemma centeredSaddlePhase_quadratic_decay (τ : ℂ)
    (hroot : charPoly params13 τ = 0) (him : 0 < τ.im)
    (hmax : ∀ σ : ℂ, charPoly params13 σ = 0 → 0 < σ.im → σ.re ≤ τ.re) :
    ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧ ∀ t : ℝ, |t| ≤ δ →
      (centeredSaddlePhase τ t - centeredSaddlePhase τ 0).re ≤ -c * t ^ 2 := by
  obtain ⟨hx, hy⟩ := saddle_params13_maximal_root_box τ hroot him hmax
  have hs := saddlePhaseSecond_params13_re_pos τ
    ⟨by linarith only [hx.1], by linarith only [hx.2]⟩
    (by rw [abs_of_pos him]; linarith only [hy.2])
  apply exists_local_quadratic_decay (b := -saddlePhaseSecond params13 τ / 2)
    _ (centeredSaddlePhase_taylor τ hroot him hmax)
  simpa using (by linarith : -(saddlePhaseSecond params13 τ).re / 2 < 0)

end ZudilinZeta
end
end

-- Component: missions.zudilin.LocalSaddleIntegral
section
set_option autoImplicit false
noncomputable section
open Complex Filter Topology MeasureTheory Set

namespace ZudilinZeta

def localSaddleIntegrand (δ : ℝ) (f : ℝ → ℂ) (a : ℕ → ℝ → ℂ) (n : ℕ) (u : ℝ) : ℂ :=
  if |u / Real.sqrt (n : ℝ)| ≤ δ then
    a n (u / Real.sqrt (n : ℝ)) *
      Complex.exp ((n : ℂ) * (f (u / Real.sqrt (n : ℝ)) - f 0))
  else 0

lemma measurable_localSaddleIntegrand {δ : ℝ} {f : ℝ → ℂ} {a : ℕ → ℝ → ℂ}
    (hf : Measurable f) (ha : ∀ n, Measurable (a n)) (n : ℕ) :
    Measurable (localSaddleIntegrand δ f a n) := by
  unfold localSaddleIntegrand
  apply Measurable.ite
  · exact measurableSet_le (by fun_prop) measurable_const
  · exact (ha n |>.comp (by fun_prop)).mul
      (Complex.measurable_exp.comp (measurable_const.mul ((hf.comp (by fun_prop)).sub_const _)))
  · exact measurable_const

lemma tendsto_localSaddleIntegrand {δ : ℝ} (hδ : 0 < δ)
    {f : ℝ → ℂ} {a : ℕ → ℝ → ℂ} {b a₀ : ℂ}
    (hf : Tendsto (fun t : ℝ =>
      (f t - f 0 - b * (t : ℂ) ^ 2) / (t : ℂ) ^ 2) (𝓝 0) (𝓝 0))
    (ha : ∀ u : ℝ, Tendsto (fun n : ℕ => a n (u / Real.sqrt (n : ℝ))) atTop (𝓝 a₀))
    (u : ℝ) :
    Tendsto (fun n : ℕ => localSaddleIntegrand δ f a n u) atTop
      (𝓝 (a₀ * Complex.exp (b * (u : ℂ) ^ 2))) := by
  have hs : Tendsto (fun n : ℕ => u / Real.sqrt (n : ℝ)) atTop (𝓝 0) :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_div_atTop u
  apply Tendsto.congr' _ ((ha u).mul (tendsto_saddle_scaled_exponential hf u))
  have hb : ∀ᶠ n : ℕ in atTop, |u / Real.sqrt (n : ℝ)| < δ :=
    hs.abs.eventually (by simpa using gt_mem_nhds hδ)
  filter_upwards [hb] with n hn
  simp only [localSaddleIntegrand, if_pos hn.le]

lemma norm_localSaddleIntegrand_le {δ c A : ℝ} {f : ℝ → ℂ} {a : ℕ → ℝ → ℂ}
    (hA : 0 ≤ A)
    (hf : ∀ t : ℝ, |t| ≤ δ → (f t - f 0).re ≤ -c * t ^ 2)
    {n : ℕ} (hn : 0 < n) (ha : ∀ t : ℝ, |t| ≤ δ → ‖a n t‖ ≤ A) (u : ℝ) :
    ‖localSaddleIntegrand δ f a n u‖ ≤ A * Real.exp (-c * u ^ 2) := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hscale : (n : ℝ) * (u / Real.sqrt (n : ℝ)) ^ 2 = u ^ 2 := by
    rw [div_pow, Real.sq_sqrt hnpos.le]
    field_simp
  by_cases hu : |u / Real.sqrt (n : ℝ)| ≤ δ
  · rw [localSaddleIntegrand, if_pos hu, norm_mul, Complex.norm_exp]
    apply mul_le_mul (ha _ hu) _ (by positivity) hA
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
    calc
      (n : ℝ) * (f (u / Real.sqrt (n : ℝ)) - f 0).re ≤
          (n : ℝ) * (-c * (u / Real.sqrt (n : ℝ)) ^ 2) :=
        mul_le_mul_of_nonneg_left (hf _ hu) hnpos.le
      _ = -c * u ^ 2 := by rw [← hscale]; ring
  · rw [localSaddleIntegrand, if_neg hu, norm_zero]
    positivity

lemma tendsto_integral_localSaddleIntegrand {δ c A : ℝ} (hδ : 0 < δ) (hc : 0 < c)
    (hA : 0 ≤ A) {f : ℝ → ℂ} {a : ℕ → ℝ → ℂ} {b a₀ : ℂ}
    (hfmeas : Measurable f) (hameas : ∀ n, Measurable (a n))
    (hf : Tendsto (fun t : ℝ =>
      (f t - f 0 - b * (t : ℂ) ^ 2) / (t : ℂ) ^ 2) (𝓝 0) (𝓝 0))
    (hquad : ∀ t : ℝ, |t| ≤ δ → (f t - f 0).re ≤ -c * t ^ 2)
    (ha : ∀ u : ℝ, Tendsto (fun n : ℕ => a n (u / Real.sqrt (n : ℝ))) atTop (𝓝 a₀))
    (habound : ∀ᶠ n : ℕ in atTop, ∀ t : ℝ, |t| ≤ δ → ‖a n t‖ ≤ A) :
    Tendsto (fun n : ℕ => ∫ u : ℝ, localSaddleIntegrand δ f a n u) atTop
      (𝓝 (∫ u : ℝ, a₀ * Complex.exp (b * (u : ℂ) ^ 2))) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun u : ℝ => A * Real.exp (-c * u ^ 2))
  · exact Eventually.of_forall fun n =>
      (measurable_localSaddleIntegrand hfmeas hameas n).aestronglyMeasurable
  · filter_upwards [eventually_gt_atTop (0 : ℕ), habound] with n hn han
    exact ae_of_all _ (norm_localSaddleIntegrand_le hA hquad hn han)
  · exact (integrable_exp_neg_mul_sq hc).const_mul A
  · exact ae_of_all _ (tendsto_localSaddleIntegrand hδ hf ha)

end ZudilinZeta
end
end

-- Component: missions.zudilin.LocalSaddleAsymptotic
section
set_option autoImplicit false
noncomputable section
open Complex Filter Topology MeasureTheory Set

namespace ZudilinZeta

lemma integral_localSaddleIntegrand_eq {δ : ℝ} (hδ : 0 ≤ δ)
    (f : ℝ → ℂ) (a : ℕ → ℝ → ℂ) (n : ℕ) :
    (∫ u : ℝ, localSaddleIntegrand δ f a n u) =
      (Real.sqrt (n : ℝ) : ℂ) * ∫ t in -δ..δ,
        a n t * Complex.exp ((n : ℂ) * (f t - f 0)) := by
  let g : ℝ → ℂ := (Icc (-δ) δ).indicator
    (fun t => a n t * Complex.exp ((n : ℂ) * (f t - f 0)))
  have hg : (∫ t : ℝ, g t) = ∫ t in -δ..δ,
      a n t * Complex.exp ((n : ℂ) * (f t - f 0)) := by
    rw [show g = (Icc (-δ) δ).indicator
      (fun t => a n t * Complex.exp ((n : ℂ) * (f t - f 0))) by rfl,
      MeasureTheory.integral_indicator measurableSet_Icc,
      integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by linarith)]
  calc
    (∫ u : ℝ, localSaddleIntegrand δ f a n u) =
        ∫ u : ℝ, g (u / Real.sqrt (n : ℝ)) := by
      congr 1
      ext u
      simp only [localSaddleIntegrand, g, Set.indicator, mem_Icc, abs_le]
    _ = |Real.sqrt (n : ℝ)| • ∫ t : ℝ, g t :=
      Measure.integral_comp_div g (Real.sqrt (n : ℝ))
    _ = _ := by rw [abs_of_nonneg (Real.sqrt_nonneg _), Complex.real_smul, hg]

lemma tendsto_local_saddle_integral {δ c A : ℝ} (hδ : 0 < δ) (hc : 0 < c)
    (hA : 0 ≤ A) {f : ℝ → ℂ} {a : ℕ → ℝ → ℂ} {b a₀ : ℂ}
    (hb : b.re < 0)
    (hfmeas : Measurable f) (hameas : ∀ n, Measurable (a n))
    (hf : Tendsto (fun t : ℝ =>
      (f t - f 0 - b * (t : ℂ) ^ 2) / (t : ℂ) ^ 2) (𝓝 0) (𝓝 0))
    (hquad : ∀ t : ℝ, |t| ≤ δ → (f t - f 0).re ≤ -c * t ^ 2)
    (ha : ∀ u : ℝ, Tendsto (fun n : ℕ => a n (u / Real.sqrt (n : ℝ))) atTop (𝓝 a₀))
    (habound : ∀ᶠ n : ℕ in atTop, ∀ t : ℝ, |t| ≤ δ → ‖a n t‖ ≤ A) :
    Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ) : ℂ) * ∫ t in -δ..δ,
      a n t * Complex.exp ((n : ℂ) * (f t - f 0))) atTop
      (𝓝 (a₀ * ((Real.pi : ℂ) / (-b)) ^ (1 / 2 : ℂ))) := by
  have h := tendsto_integral_localSaddleIntegrand hδ hc hA hfmeas hameas hf hquad ha habound
  have he : (∫ u : ℝ, a₀ * Complex.exp (b * (u : ℂ) ^ 2)) =
      a₀ * ((Real.pi : ℂ) / (-b)) ^ (1 / 2 : ℂ) := by
    rw [MeasureTheory.integral_const_mul]
    congr 1
    simpa only [neg_neg] using integral_gaussian_complex (b := -b) (by simpa using neg_pos.mpr hb)
  rw [he] at h
  simpa only [integral_localSaddleIntegrand_eq hδ.le] using h

end ZudilinZeta
end
end

-- Component: missions.zudilin.Params13LocalSaddle
section
set_option autoImplicit false
noncomputable section
open Complex Filter Topology MeasureTheory

namespace ZudilinZeta

lemma params13_local_saddle_asymptotic (τ : ℂ)
    (hroot : charPoly params13 τ = 0) (him : 0 < τ.im)
    (hmax : ∀ σ : ℂ, charPoly params13 σ = 0 → 0 < σ.im → σ.re ≤ τ.re) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (a : ℕ → ℝ → ℂ) (a₀ : ℂ) (A : ℝ), 0 ≤ A →
      (∀ n, Measurable (a n)) →
      (∀ u : ℝ, Tendsto (fun n : ℕ => a n (u / Real.sqrt (n : ℝ))) atTop (𝓝 a₀)) →
      (∀ᶠ n : ℕ in atTop, ∀ t : ℝ, |t| ≤ δ → ‖a n t‖ ≤ A) →
      Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ) : ℂ) * ∫ t in -δ..δ,
        a n t * Complex.exp ((n : ℂ) *
          (adjustedSaddlePhase params13 (τ + (t : ℂ) * I) - f0 params13 τ))) atTop
        (𝓝 (a₀ * ((Real.pi : ℂ) / (saddlePhaseSecond params13 τ / 2)) ^ (1 / 2 : ℂ))) := by
  obtain ⟨δ, c, hδ, hc, hquad⟩ := centeredSaddlePhase_quadratic_decay τ hroot him hmax
  obtain ⟨hx, hy⟩ := saddle_params13_maximal_root_box τ hroot him hmax
  have hx' : 87 < τ.re ∧ τ.re < 175 / 2 :=
    ⟨by linarith only [hx.1], by linarith only [hx.2]⟩
  have hs := saddlePhaseSecond_params13_re_pos τ ⟨hx'.1.le, hx'.2.le⟩
    (by rw [abs_of_pos him]; linarith only [hy.2])
  have hb : (-saddlePhaseSecond params13 τ / 2).re < 0 := by
    simpa using (by linarith : -(saddlePhaseSecond params13 τ).re / 2 < 0)
  have hzero : centeredSaddlePhase τ 0 = f0 params13 τ := by
    simpa [centeredSaddlePhase, adjustedSaddlePhase] using
      saddlePhase_params13_stationary_value τ hroot him hmax
  refine ⟨δ, hδ, ?_⟩
  intro a a₀ A hA hameas ha habound
  have h := tendsto_local_saddle_integral hδ hc hA hb
    (contDiff_centeredSaddlePhase hx').continuous.measurable hameas
    (centeredSaddlePhase_taylor τ hroot him hmax) hquad ha habound
  rw [hzero] at h
  simpa only [centeredSaddlePhase, neg_div, neg_neg] using h

end ZudilinZeta
end
end

-- Component: missions.zudilin.Params13VerticalMaximum
section
set_option autoImplicit false

namespace ZudilinZeta

private noncomputable def verticalAngle (x y : ℝ) : ℝ :=
  3*(Real.arctan (y/x)+Real.arctan (y/(91-x)))+
  3*(Real.arctan (y/(x-64))-Real.arctan (y/(x-27)))+
  ∑ j∈Finset.Icc (29 : ℕ) 38,
    (Real.arctan (y/(x-91+j))-Real.arctan (y/(x-j)))

private lemma verticalAngle_eq (x y : ℝ) (hx : 87≤x ∧ x≤175/2) :
    (saddlePhaseDeriv params13 ((x : ℂ)+(y : ℂ)*Complex.I)).im=verticalAngle x y := by
  simpa [verticalAngle] using saddlePhaseDeriv_params13_im_formula
    ((x : ℂ)+(y : ℂ)*Complex.I) (by simpa using hx)

private lemma angle_difference_nonneg (x y e : ℝ)
    (hx : 87≤x) (hy : 0≤y) (he : 27≤e ∧ e≤38) :
    0≤Real.arctan (y/(x-91+e))-Real.arctan (y/(x-e)) := by
  apply sub_nonneg.mpr
  apply Real.arctan_le_arctan_iff.mpr
  exact div_le_div_of_nonneg_left hy (by linarith only [hx, he.1])
    (by linarith only [he.2])

private lemma verticalAngle_lower (x y : ℝ) (hx : 87≤x ∧ x≤175/2) (hy : 0≤y) :
    3*Real.arctan (y/(91-x))≤verticalAngle x y := by
  have ht : 0≤Real.arctan (y/x) :=
    Real.arctan_nonneg.mpr (div_nonneg hy (by linarith only [hx.1]))
  have h27 := angle_difference_nonneg x y 27 hx.1 hy (by norm_num)
  rw [show x-91+27=x-64 by ring] at h27
  have hs : 0≤∑ j∈Finset.Icc (29 : ℕ) 38,
      (Real.arctan (y/(x-91+j))-Real.arctan (y/(x-j))) := by
    apply Finset.sum_nonneg
    intro j hj
    have hj' := Finset.mem_Icc.mp hj
    apply angle_difference_nonneg x y (j : ℝ) hx.1 hy
    constructor
    · exact_mod_cast (show 27≤j by omega)
    · exact_mod_cast hj'.2
  unfold verticalAngle
  linarith only [ht, h27, hs]

private lemma verticalAngle_neg (x y : ℝ) : verticalAngle x (-y)=-verticalAngle x y := by
  norm_num [verticalAngle, Finset.sum_Icc_succ_top, neg_div, Real.arctan_neg]
  ring

lemma saddlePhaseDeriv_im_vertical_nonpos (x y : ℝ)
    (hx : 87≤x ∧ x≤175/2) (hy : y≤0) :
    (saddlePhaseDeriv params13 ((x : ℂ)+(y : ℂ)*Complex.I)).im≤0 := by
  rw [verticalAngle_eq x y hx]
  have hh := verticalAngle_lower x (-y) hx (by linarith only [hy])
  have ht : 0≤Real.arctan ((-y)/(91-x)) :=
    Real.arctan_nonneg.mpr (div_nonneg (by linarith only [hy])
      (by linarith only [hx.2]))
  rw [verticalAngle_neg] at hh
  linarith only [hh, ht]

lemma saddlePhaseDeriv_im_vertical_gt_pi (x y : ℝ)
    (hx : 87≤x ∧ x≤175/2) (hy : 10≤y) :
    Real.pi<(saddlePhaseDeriv params13 ((x : ℂ)+(y : ℂ)*Complex.I)).im := by
  rw [verticalAngle_eq x y hx]
  have hh := verticalAngle_lower x y hx (by linarith only [hy])
  have hd : 0<91-x := by linarith only [hx.2]
  have hratio : 2<y/(91-x) := by
    apply (lt_div_iff₀ hd).mpr
    linarith only [hy, hx.1]
  have hsqrt : Real.sqrt 3<2 := by
    have hs := Real.sq_sqrt (show (0 : ℝ)≤3 by norm_num)
    have hp := Real.sqrt_nonneg (3 : ℝ)
    nlinarith only [hs, hp]
  have ht : Real.pi/3<Real.arctan (y/(91-x)) := by
    rw [← Real.arctan_sqrt_three]
    exact Real.arctan_lt_arctan_iff.mpr (hsqrt.trans hratio)
  linarith only [hh, ht]

lemma adjustedSaddlePhase_vertical_derivative_signs (τ : ℂ)
    (hroot : charPoly params13 τ=0) (him : 0<τ.im)
    (hmax : ∀ σ : ℂ, charPoly params13 σ=0 → 0<σ.im → σ.re≤τ.re) :
    (∀ y : ℝ, y<τ.im →
      0<Real.pi-(saddlePhaseDeriv params13 ((τ.re : ℂ)+(y : ℂ)*Complex.I)).im) ∧
    (∀ y : ℝ, τ.im<y →
      Real.pi-(saddlePhaseDeriv params13 ((τ.re : ℂ)+(y : ℂ)*Complex.I)).im<0) := by
  obtain ⟨hx0, hy0⟩ := saddle_params13_maximal_root_box τ hroot him hmax
  have hx : 87≤τ.re ∧ τ.re≤175/2 :=
    ⟨by linarith only [hx0.1], by linarith only [hx0.2]⟩
  have ht : τ.im∈Set.Icc (-10 : ℝ) 10 :=
    ⟨by linarith only [him], by linarith only [hy0.2]⟩
  have he : (τ.re : ℂ)+(τ.im : ℂ)*Complex.I=τ := by
    apply Complex.ext <;> simp
  have hvalue : (saddlePhaseDeriv params13 ((τ.re : ℂ)+(τ.im : ℂ)*Complex.I)).im=Real.pi := by
    rw [he, saddlePhaseDeriv_params13_eq_pi_mul_I τ hroot him hmax]
    simp
  have hm := strictMonoOn_saddlePhaseDeriv_im_vertical τ.re hx
  constructor
  · intro y hy
    by_cases hlo : y< -10
    · have hh := saddlePhaseDeriv_im_vertical_nonpos τ.re y hx (by linarith only [hlo])
      linarith only [hh, Real.pi_pos]
    · have hym : y∈Set.Icc (-10 : ℝ) 10 :=
        ⟨by linarith only [hlo], by linarith only [hy, ht.2]⟩
      have hh := hm hym ht hy
      dsimp only at hh
      rw [hvalue] at hh
      linarith only [hh]
  · intro y hy
    by_cases hhi : 10<y
    · have hh := saddlePhaseDeriv_im_vertical_gt_pi τ.re y hx hhi.le
      linarith only [hh]
    · have hym : y∈Set.Icc (-10 : ℝ) 10 :=
        ⟨by linarith only [hy, him], by linarith only [hhi]⟩
      have hh := hm ht hym hy
      dsimp only at hh
      rw [hvalue] at hh
      linarith only [hh]

lemma adjustedSaddlePhase_vertical_strict_max (τ : ℂ)
    (hroot : charPoly params13 τ=0) (him : 0<τ.im)
    (hmax : ∀ σ : ℂ, charPoly params13 σ=0 → 0<σ.im → σ.re≤τ.re)
    (y : ℝ) (hy : y≠τ.im) :
    (adjustedSaddlePhase params13 ((τ.re : ℂ)+(y : ℂ)*Complex.I)).re<
      (f0 params13 τ).re := by
  obtain ⟨hx0, hy0⟩ := saddle_params13_maximal_root_box τ hroot him hmax
  have hx : 87≤τ.re ∧ τ.re≤175/2 :=
    ⟨by linarith only [hx0.1], by linarith only [hx0.2]⟩
  obtain ⟨hslo, hshi⟩ := adjustedSaddlePhase_vertical_derivative_signs τ hroot him hmax
  let g : ℝ → ℝ := fun t =>
    (adjustedSaddlePhase params13 ((τ.re : ℂ)+(t : ℂ)*Complex.I)).re
  have hderiv (t : ℝ) : HasDerivAt g
      (Real.pi-(saddlePhaseDeriv params13 ((τ.re : ℂ)+(t : ℂ)*Complex.I)).im) t :=
    hasDerivAt_adjustedSaddlePhase_vertical τ.re t hx
  have hleft : StrictMonoOn g (Set.Iic τ.im) := by
    apply strictMonoOn_of_deriv_pos (convex_Iic τ.im)
      (fun t ht => (hderiv t).continuousAt.continuousWithinAt)
    intro t ht
    rw [(hderiv t).deriv]
    apply hslo t
    simpa only [interior_Iic, Set.mem_Iio] using ht
  have hright : StrictAntiOn g (Set.Ici τ.im) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici τ.im)
      (fun t ht => (hderiv t).continuousAt.continuousWithinAt)
    intro t ht
    rw [(hderiv t).deriv]
    apply hshi t
    simpa only [interior_Ici, Set.mem_Ioi] using ht
  have he : (τ.re : ℂ)+(τ.im : ℂ)*Complex.I=τ := by
    apply Complex.ext <;> simp
  have hvalue : g τ.im=(f0 params13 τ).re := by
    change (adjustedSaddlePhase params13 ((τ.re : ℂ)+(τ.im : ℂ)*Complex.I)).re=_
    rw [he]
    exact congrArg Complex.re (saddlePhase_params13_stationary_value τ hroot him hmax)
  change g y<(f0 params13 τ).re
  rw [← hvalue]
  rcases lt_or_gt_of_ne hy with hy | hy
  · exact hleft hy.le (by simp) hy
  · exact hright (by simp) hy.le hy

lemma pi_lt_three_arctan_two : Real.pi < 3 * Real.arctan 2 := by
  have hsqrt : Real.sqrt 3 < 2 := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    have hp := Real.sqrt_nonneg (3 : ℝ)
    nlinarith only [hs, hp]
  have ht : Real.pi / 3 < Real.arctan 2 := by
    rw [← Real.arctan_sqrt_three]
    exact Real.arctan_lt_arctan_iff.mpr hsqrt
  linarith only [ht]

lemma saddlePhaseDeriv_im_vertical_tail_lower (x y : ℝ)
    (hx : 87 ≤ x ∧ x ≤ 175 / 2) (hy : 10 ≤ y) :
    3 * Real.arctan 2 ≤
      (saddlePhaseDeriv params13 ((x : ℂ) + (y : ℂ) * Complex.I)).im := by
  rw [verticalAngle_eq x y hx]
  have hh := verticalAngle_lower x y hx (by linarith only [hy])
  have hd : 0 < 91 - x := by linarith only [hx.2]
  have hratio : 2 ≤ y / (91 - x) := by
    apply (le_div_iff₀ hd).mpr
    linarith only [hy, hx.1]
  have ht := Real.arctan_le_arctan_iff.mpr hratio
  linarith only [hh, ht]

end ZudilinZeta
end

-- Component: missions.zudilin.Params13PhaseGap
section
set_option autoImplicit false
noncomputable section
open Complex Filter Topology Set

namespace ZudilinZeta

lemma centeredSaddlePhase_uniform_gap (τ : ℂ)
    (hroot : charPoly params13 τ = 0) (him : 0 < τ.im)
    (hmax : ∀ σ : ℂ, charPoly params13 σ = 0 → 0 < σ.im → σ.re ≤ τ.re)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, δ ≤ |t| →
      (centeredSaddlePhase τ t - centeredSaddlePhase τ 0).re ≤ -ε := by
  obtain ⟨hx0, hy0⟩ := saddle_params13_maximal_root_box τ hroot him hmax
  have hx : 87 ≤ τ.re ∧ τ.re ≤ 175 / 2 :=
    ⟨by linarith only [hx0.1], by linarith only [hx0.2]⟩
  obtain ⟨hlo, hhi⟩ := adjustedSaddlePhase_vertical_derivative_signs τ hroot him hmax
  let g : ℝ → ℝ := fun t => (centeredSaddlePhase τ t).re
  have hrep (t : ℝ) : τ + (t : ℂ) * I =
      (τ.re : ℂ) + ((τ.im + t : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp <;> ring
  have hd (t : ℝ) : HasDerivAt g
      (Real.pi - (saddlePhaseDeriv params13 (τ + (t : ℂ) * I)).im) t := by
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_centeredSaddlePhase hx t)
    convert! h using 1
    simp only [Complex.reCLM_apply, Complex.mul_re, Complex.mul_im, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_one, mul_zero, sub_zero, zero_sub]
    ring
  have hleft : StrictMonoOn g (Iic 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Iic (0 : ℝ))
      (fun t _ => (hd t).continuousAt.continuousWithinAt)
    intro t ht
    have ht' : t < 0 := by simpa only [interior_Iic, mem_Iio] using ht
    rw [(hd t).deriv, hrep]
    exact hlo (τ.im + t) (by linarith)
  have hright : StrictAntiOn g (Ici 0) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici (0 : ℝ))
      (fun t _ => (hd t).continuousAt.continuousWithinAt)
    intro t ht
    have ht' : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
    rw [(hd t).deriv, hrep]
    exact hhi (τ.im + t) (by linarith)
  have hmδ : g (-δ) < g 0 := hleft (by change -δ ≤ 0; linarith) (by simp) (by linarith)
  have hpδ : g δ < g 0 := hright (by simp) (by exact hδ.le) hδ
  let ε := min (g 0 - g (-δ)) (g 0 - g δ)
  have hε : 0 < ε := lt_min (sub_pos.mpr hmδ) (sub_pos.mpr hpδ)
  refine ⟨ε, hε, ?_⟩
  intro t ht
  change g t - g 0 ≤ -ε
  rcases le_total t 0 with hneg | hpos
  · have htd : t ≤ -δ := by rw [abs_of_nonpos hneg] at ht; linarith
    have hh := hleft.monotoneOn hneg (by change -δ ≤ 0; linarith) htd
    have hb : ε ≤ g 0 - g (-δ) := min_le_left _ _
    linarith
  · have hdt : δ ≤ t := by simpa only [abs_of_nonneg hpos] using ht
    have hh := hright.antitoneOn hδ.le hpos hdt
    have hb : ε ≤ g 0 - g δ := min_le_right _ _
    linarith

end ZudilinZeta
end
end

-- Component: missions.zudilin.Params13TailPhase
section
set_option autoImplicit false
noncomputable section
open Complex Filter Topology Set

namespace ZudilinZeta

private def verticalRealPhase (x y : ℝ) : ℝ :=
  (adjustedSaddlePhase params13 ((x : ℂ) + (y : ℂ) * I)).re

lemma vertical_phase_upper_tail (x : ℝ) (hx : 87 ≤ x ∧ x ≤ 175 / 2)
    (y : ℝ) (hy : 10 ≤ y) :
    verticalRealPhase x y ≤ verticalRealPhase x 10 -
      (3 * Real.arctan 2 - Real.pi) * (y - 10) := by
  let k := 3 * Real.arctan 2 - Real.pi
  let h : ℝ → ℝ := fun t => verticalRealPhase x t + k * t
  have hd (t : ℝ) : HasDerivAt h
      (Real.pi - (saddlePhaseDeriv params13 ((x : ℂ) + (t : ℂ) * I)).im + k) t := by
    convert! (hasDerivAt_adjustedSaddlePhase_vertical x t hx).add
      ((hasDerivAt_id t).const_mul k) using 1 <;> simp [h, verticalRealPhase]
  have hm : AntitoneOn h (Ici 10) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici (10 : ℝ))
      (fun t _ => (hd t).continuousAt.continuousWithinAt)
      (fun t _ => (hd t).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hd t).deriv]
    have hb := saddlePhaseDeriv_im_vertical_tail_lower x t hx (interior_subset ht)
    dsimp [k]
    linarith
  have hh := hm (by simp : (10 : ℝ) ∈ Ici 10) hy hy
  dsimp [h, k] at hh
  linarith

lemma vertical_phase_lower_tail (x : ℝ) (hx : 87 ≤ x ∧ x ≤ 175 / 2)
    (y : ℝ) (hy : y ≤ 0) :
    verticalRealPhase x y ≤ verticalRealPhase x 0 + Real.pi * y := by
  let h : ℝ → ℝ := fun t => verticalRealPhase x t - Real.pi * t
  have hd (t : ℝ) : HasDerivAt h
      (Real.pi - (saddlePhaseDeriv params13 ((x : ℂ) + (t : ℂ) * I)).im - Real.pi) t := by
    convert! (hasDerivAt_adjustedSaddlePhase_vertical x t hx).sub
      ((hasDerivAt_id t).const_mul Real.pi) using 1 <;> simp [h, verticalRealPhase]
  have hm : MonotoneOn h (Iic 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Iic (0 : ℝ))
      (fun t _ => (hd t).continuousAt.continuousWithinAt)
      (fun t _ => (hd t).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hd t).deriv]
    have ht' : t ∈ Iic (0 : ℝ) := interior_subset ht
    have hb := saddlePhaseDeriv_im_vertical_nonpos x t hx ht'
    linarith
  have hh := hm hy (by simp : (0 : ℝ) ∈ Iic 0) hy
  dsimp [h] at hh
  linarith

lemma centeredSaddlePhase_linear_decay (τ : ℂ)
    (hroot : charPoly params13 τ = 0) (him : 0 < τ.im)
    (hmax : ∀ σ : ℂ, charPoly params13 σ = 0 → 0 < σ.im → σ.re ≤ τ.re) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ t : ℝ,
      (centeredSaddlePhase τ t - centeredSaddlePhase τ 0).re ≤ C - c * |t| := by
  obtain ⟨hx0, hy0⟩ := saddle_params13_maximal_root_box τ hroot him hmax
  have hx : 87 ≤ τ.re ∧ τ.re ≤ 175 / 2 :=
    ⟨by linarith only [hx0.1], by linarith only [hx0.2]⟩
  let k : ℝ := 3 * Real.arctan 2 - Real.pi
  have hk : 0 < k := sub_pos.mpr pi_lt_three_arctan_two
  let c : ℝ := min Real.pi k
  have hc : 0 < c := lt_min Real.pi_pos hk
  have hcπ : c ≤ Real.pi := min_le_left _ _
  have hck : c ≤ k := min_le_right _ _
  have hval : centeredSaddlePhase τ 0 = f0 params13 τ := by
    simpa [centeredSaddlePhase, adjustedSaddlePhase] using
      saddlePhase_params13_stationary_value τ hroot him hmax
  have hmax' (y : ℝ) : verticalRealPhase τ.re y ≤ (f0 params13 τ).re := by
    by_cases he : y = τ.im
    · subst y
      have hz : (τ.re : ℂ) + (τ.im : ℂ) * I = τ := Complex.re_add_im τ
      change (adjustedSaddlePhase params13 ((τ.re : ℂ) + (τ.im : ℂ) * I)).re ≤ _
      rw [hz]
      exact le_of_eq (congrArg Complex.re (saddlePhase_params13_stationary_value τ hroot him hmax))
    · exact (adjustedSaddlePhase_vertical_strict_max τ hroot him hmax y he).le
  have hglobal (y : ℝ) : verticalRealPhase τ.re y ≤
      (f0 params13 τ).re + 10 * k - c * |y| := by
    by_cases hy0 : y ≤ 0
    · have hh := vertical_phase_lower_tail τ.re hx y hy0
      have hmul := mul_le_mul_of_nonneg_right hcπ (abs_nonneg y)
      rw [abs_of_nonpos hy0] at hmul ⊢
      have h0 := hmax' 0
      nlinarith
    · have hypos : 0 < y := lt_of_not_ge hy0
      rw [abs_of_pos hypos]
      by_cases hy10 : 10 ≤ y
      · have hh := vertical_phase_upper_tail τ.re hx y hy10
        have h10 := hmax' 10
        have hmul := mul_le_mul_of_nonneg_right hck hypos.le
        dsimp [k] at hh ⊢
        nlinarith
      · have hh := hmax' y
        have hmul : c * y ≤ 10 * k := by nlinarith [mul_le_mul_of_nonneg_left (le_of_not_ge hy10) hc.le]
        linarith
  refine ⟨c, 10 * k + c * |τ.im|, hc, by positivity, ?_⟩
  intro t
  have hh := hglobal (τ.im + t)
  have hz : τ + (t : ℂ) * I = (τ.re : ℂ) + ((τ.im + t : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp <;> ring
  have he : (centeredSaddlePhase τ t - centeredSaddlePhase τ 0).re =
      verticalRealPhase τ.re (τ.im + t) - (f0 params13 τ).re := by
    rw [Complex.sub_re, hval]
    congr 1
    unfold centeredSaddlePhase verticalRealPhase
    rw [hz]
  rw [he]
  have habs : |t| ≤ |τ.im + t| + |τ.im| := by
    have h := abs_add_le (τ.im + t) (-τ.im)
    rw [show τ.im + t + -τ.im = t by ring, abs_neg] at h
    exact h
  have hmul := mul_le_mul_of_nonneg_left habs hc.le
  linarith

end ZudilinZeta
end
end

-- Component: missions.zudilin.SaddleTailIntegral
section
set_option autoImplicit false
noncomputable section
open Complex Filter Topology MeasureTheory Set

namespace ZudilinZeta

def tailSaddleIntegrand (δ : ℝ) (f : ℝ → ℂ) (a : ℕ → ℝ → ℂ)
    (n : ℕ) (t : ℝ) : ℂ :=
  if δ < |t| then a n t * Complex.exp ((n : ℂ) * (f t - f 0)) else 0

lemma norm_tailSaddleIntegrand_le {δ ε : ℝ} {f : ℝ → ℂ}
    {a : ℕ → ℝ → ℂ} {B : ℝ → ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hB : ∀ t, 0 ≤ B t)
    (hgap : ∀ t, δ ≤ |t| → (f t - f 0).re ≤ -ε)
    (habound : ∀ t, ‖a n t‖ * Real.exp ((f t - f 0).re / 2) ≤ B t)
    (t : ℝ) :
    ‖tailSaddleIntegrand δ f a n t‖ ≤
      Real.exp (-ε * ((n : ℝ) - 1 / 2)) * B t := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  by_cases ht : δ < |t|
  · rw [tailSaddleIntegrand, if_pos ht, norm_mul, Complex.norm_exp]
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
    calc
      ‖a n t‖ * Real.exp ((n : ℝ) * (f t - f 0).re) =
          Real.exp (((n : ℝ) - 1 / 2) * (f t - f 0).re) *
            (‖a n t‖ * Real.exp ((f t - f 0).re / 2)) := by
        rw [← mul_assoc, mul_comm _ ‖a n t‖, mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-ε * ((n : ℝ) - 1 / 2)) * B t := by
        apply mul_le_mul _ (habound t) (by positivity) (by positivity)
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left (hgap t ht.le)
          (show 0 ≤ (n : ℝ) - 1 / 2 by linarith)]
  · rw [tailSaddleIntegrand, if_neg ht, norm_zero]
    exact mul_nonneg (Real.exp_pos _).le (hB t)

lemma tendsto_sqrt_mul_exp_tail {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) *
      Real.exp (-ε * ((n : ℝ) - 1 / 2))) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (1 / 2 : ℝ) ε hε).comp tendsto_natCast_atTop_atTop
  have hh := h.mul_const (Real.exp (ε / 2))
  simpa only [Function.comp_def, zero_mul, Real.sqrt_eq_rpow, mul_assoc, ← Real.exp_add,
    show ∀ x : ℝ, -ε * x + ε / 2 = -ε * (x - 1 / 2) from fun x => by ring] using hh

lemma tendsto_integral_tailSaddleIntegrand {δ ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℂ} {a : ℕ → ℝ → ℂ} {B : ℝ → ℝ}
    (hB : ∀ t, 0 ≤ B t) (hBi : Integrable B)
    (hgap : ∀ t, δ ≤ |t| → (f t - f 0).re ≤ -ε)
    (habound : ∀ᶠ n : ℕ in atTop, ∀ t,
      ‖a n t‖ * Real.exp ((f t - f 0).re / 2) ≤ B t) :
    Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ) : ℂ) *
      ∫ t : ℝ, tailSaddleIntegrand δ f a n t) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hb : ∀ᶠ n : ℕ in atTop,
      ‖(Real.sqrt (n : ℝ) : ℂ) * ∫ t : ℝ, tailSaddleIntegrand δ f a n t‖ ≤
        (Real.sqrt (n : ℝ) * Real.exp (-ε * ((n : ℝ) - 1 / 2))) * ∫ t, B t := by
    filter_upwards [eventually_ge_atTop (1 : ℕ), habound] with n hn han
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    have hh := norm_integral_le_of_norm_le
      (hBi.const_mul (Real.exp (-ε * ((n : ℝ) - 1 / 2))))
      (ae_of_all _ (norm_tailSaddleIntegrand_le hn hB hgap han))
    simpa only [integral_const_mul] using hh
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hb
    (by simpa using (tendsto_sqrt_mul_exp_tail hε).mul_const (∫ t, B t))

lemma integrable_saddle_integrand {f : ℝ → ℂ} {a : ℕ → ℝ → ℂ} {B : ℝ → ℝ}
    (hf : Measurable f) (ha : ∀ n, Measurable (a n))
    (hBi : Integrable B) (hmax : ∀ t, (f t - f 0).re ≤ 0)
    {n : ℕ} (hn : 1 ≤ n)
    (habound : ∀ t, ‖a n t‖ * Real.exp ((f t - f 0).re / 2) ≤ B t) :
    Integrable (fun t => a n t * Complex.exp ((n : ℂ) * (f t - f 0))) := by
  apply hBi.mono'
  · exact ((ha n).mul (Complex.measurable_exp.comp
      (measurable_const.mul (hf.sub_const _)))).aestronglyMeasurable
  · apply ae_of_all
    intro t
    rw [norm_mul, Complex.norm_exp]
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
    apply le_trans _ (habound t)
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [mul_nonpos_of_nonneg_of_nonpos
      (show 0 ≤ (n : ℝ) - 1 / 2 by linarith) (hmax t)]

lemma integral_saddle_eq_local_add_tail {δ : ℝ} (hδ : 0 ≤ δ)
    (f : ℝ → ℂ) (a : ℕ → ℝ → ℂ) (n : ℕ)
    (hi : Integrable (fun t => a n t * Complex.exp ((n : ℂ) * (f t - f 0)))) :
    (∫ t : ℝ, a n t * Complex.exp ((n : ℂ) * (f t - f 0))) =
      (∫ t in -δ..δ, a n t * Complex.exp ((n : ℂ) * (f t - f 0))) +
      ∫ t : ℝ, tailSaddleIntegrand δ f a n t := by
  have ht : tailSaddleIntegrand δ f a n = (Icc (-δ) δ)ᶜ.indicator
      (fun t => a n t * Complex.exp ((n : ℂ) * (f t - f 0))) := by
    ext t
    simp only [tailSaddleIntegrand, Set.indicator, mem_compl_iff, mem_Icc, ← abs_le,
      not_le]
  rw [ht, integral_indicator measurableSet_Icc.compl,
    intervalIntegral.integral_of_le (by linarith : -δ ≤ δ),
    ← integral_Icc_eq_integral_Ioc]
  exact (integral_add_compl measurableSet_Icc hi).symm

end ZudilinZeta
end
end

-- Component: missions.zudilin.ExponentialEnvelope
section
set_option autoImplicit false
noncomputable section
open Filter Topology MeasureTheory Set

namespace ZudilinZeta

lemma integrable_abs_pow_mul_exp_neg_abs (k : ℕ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ℝ => |t| ^ k * Real.exp (-c * |t|)) := by
  have hi : IntegrableOn (fun t : ℝ => t ^ k * Real.exp (-c * t)) (Ioi 0) := by
    simpa only [Real.rpow_natCast, Real.rpow_one] using
      integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := 1) (s := (k : ℝ)) (b := c)
        (by linarith [Nat.cast_nonneg (α := ℝ) k]) zero_lt_one hc
  have hp : IntegrableOn (fun t : ℝ => |t| ^ k * Real.exp (-c * |t|)) (Ioi 0) := by
    apply hi.congr_fun _ measurableSet_Ioi
    intro t ht
    simp only [abs_of_pos (mem_Ioi.mp ht)]
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_, hp⟩
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (Homeomorph.neg ℝ).measurableEmbedding]
  simpa only [Function.comp_def, abs_neg, neg_preimage, neg_Iio, neg_zero] using hp

lemma integrable_one_add_abs_pow_mul_exp_neg_abs (k : ℕ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ℝ => (1 + |t|) ^ k * Real.exp (-c * |t|)) := by
  have h0 : Integrable (fun t : ℝ => Real.exp (-c * |t|)) := by
    simpa using integrable_abs_pow_mul_exp_neg_abs 0 hc
  have hk := integrable_abs_pow_mul_exp_neg_abs k hc
  apply ((h0.add hk).const_mul ((2 : ℝ) ^ (k - 1))).mono'
  · exact (by fun_prop : Continuous (fun t : ℝ =>
      (1 + |t|) ^ k * Real.exp (-c * |t|))).aestronglyMeasurable
  · apply ae_of_all
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hb := mul_le_mul_of_nonneg_right
      (add_pow_le (a := (1 : ℝ)) (b := |t|) zero_le_one (abs_nonneg t) k)
      (Real.exp_pos (-c * |t|)).le
    simpa only [Pi.add_apply, one_pow, add_mul, one_mul, mul_assoc] using hb

lemma integrable_polynomial_phase_envelope {H : ℝ → ℝ}
    (hH : Measurable H) {c C A : ℝ} (hc : 0 < c) (hA : 0 ≤ A) (k : ℕ)
    (hdecay : ∀ t, H t ≤ C - c * |t|) :
    Integrable (fun t : ℝ => A * (1 + |t|) ^ k * Real.exp (H t / 2)) := by
  have hi := (integrable_one_add_abs_pow_mul_exp_neg_abs k (half_pos hc)).const_mul
    (A * Real.exp (C / 2))
  apply hi.mono'
  · apply Measurable.aestronglyMeasurable
    exact (measurable_const.mul ((measurable_const.add measurable_id.abs).pow_const k)).mul
      ((hH.div_const 2).exp)
  · apply ae_of_all
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc
      A * (1 + |t|) ^ k * Real.exp (H t / 2) ≤
          A * (1 + |t|) ^ k * Real.exp ((C - c * |t|) / 2) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hdecay t]))
        positivity
      _ = (A * Real.exp (C / 2)) * ((1 + |t|) ^ k * Real.exp (-(c / 2) * |t|)) := by
        rw [show (C - c * |t|) / 2 = C / 2 + -(c / 2) * |t| by ring, Real.exp_add]
        ring

end ZudilinZeta
end
end

-- Component: missions.zudilin.Params13FullSaddle
section
set_option autoImplicit false
noncomputable section
open Complex Filter Topology MeasureTheory Set

namespace ZudilinZeta

lemma params13_full_saddle_asymptotic (τ : ℂ)
    (hroot : charPoly params13 τ = 0) (him : 0 < τ.im)
    (hmax : ∀ σ : ℂ, charPoly params13 σ = 0 → 0 < σ.im → σ.re ≤ τ.re)
    (a : ℕ → ℝ → ℂ) (a₀ : ℂ) (A : ℝ) (k : ℕ) (hA : 0 ≤ A)
    (hameas : ∀ n, Measurable (a n))
    (ha : ∀ u : ℝ, Tendsto (fun n : ℕ => a n (u / Real.sqrt (n : ℝ))) atTop (𝓝 a₀))
    (habound : ∀ᶠ n : ℕ in atTop, ∀ t : ℝ, ‖a n t‖ ≤ A * (1 + |t|) ^ k) :
    Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ) : ℂ) * ∫ t : ℝ,
      a n t * Complex.exp ((n : ℂ) *
        (adjustedSaddlePhase params13 (τ + (t : ℂ) * I) - f0 params13 τ))) atTop
      (𝓝 (a₀ * ((Real.pi : ℂ) / (saddlePhaseSecond params13 τ / 2)) ^ (1 / 2 : ℂ))) := by
  let f := centeredSaddlePhase τ
  let H : ℝ → ℝ := fun t => (f t - f 0).re
  have hzero : f 0 = f0 params13 τ := by
    simpa [f, centeredSaddlePhase, adjustedSaddlePhase] using
      saddlePhase_params13_stationary_value τ hroot him hmax
  obtain ⟨hx, _⟩ := saddle_params13_maximal_root_box τ hroot him hmax
  have hf : Measurable f := (contDiff_centeredSaddlePhase
    (τ := τ) ⟨by linarith only [hx.1], by linarith only [hx.2]⟩).continuous.measurable
  obtain ⟨δ, hδ, hlocal⟩ := params13_local_saddle_asymptotic τ hroot him hmax
  have hl := hlocal a a₀ (A * (1 + δ) ^ k) (by positivity) hameas ha (by
    filter_upwards [habound] with n han t ht
    exact (han t).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith) k) hA))
  have hl' : Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ) : ℂ) * ∫ t in -δ..δ,
      a n t * Complex.exp ((n : ℂ) * (f t - f 0))) atTop
      (𝓝 (a₀ * ((Real.pi : ℂ) / (saddlePhaseSecond params13 τ / 2)) ^ (1 / 2 : ℂ))) := by
    simpa only [hzero, f, centeredSaddlePhase] using hl
  obtain ⟨c, C, hc, _, hdecay⟩ := centeredSaddlePhase_linear_decay τ hroot him hmax
  let B : ℝ → ℝ := fun t => A * (1 + |t|) ^ k * Real.exp (H t / 2)
  have hBi : Integrable B := integrable_polynomial_phase_envelope
    (Complex.measurable_re.comp (hf.sub_const _)) hc hA k hdecay
  have hB : ∀ t, 0 ≤ B t := fun t => by dsimp [B]; positivity
  have haB : ∀ᶠ n : ℕ in atTop, ∀ t,
      ‖a n t‖ * Real.exp ((f t - f 0).re / 2) ≤ B t := by
    filter_upwards [habound] with n han t
    exact mul_le_mul_of_nonneg_right (han t) (Real.exp_pos _).le
  obtain ⟨ε, hε, hgap⟩ := centeredSaddlePhase_uniform_gap τ hroot him hmax δ hδ
  have ht := tendsto_integral_tailSaddleIntegrand hε hB hBi hgap haB
  have hm (t : ℝ) : (f t - f 0).re ≤ 0 := by
    by_cases he : t = 0
    · simp [he]
    · obtain ⟨e, hepos, hegap⟩ := centeredSaddlePhase_uniform_gap
        τ hroot him hmax |t| (abs_pos.mpr he)
      exact (hegap t le_rfl).trans (by linarith)
  have hs := hl'.add ht
  simp only [add_zero] at hs
  have hs' : Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ) : ℂ) * ∫ t : ℝ,
      a n t * Complex.exp ((n : ℂ) * (f t - f 0))) atTop
      (𝓝 (a₀ * ((Real.pi : ℂ) / (saddlePhaseSecond params13 τ / 2)) ^ (1 / 2 : ℂ))) := by
    apply hs.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ), haB] with n hn han
    rw [integral_saddle_eq_local_add_tail hδ.le f a n
      (integrable_saddle_integrand hf hameas hBi hm hn han), mul_add]
  simpa only [hzero, f, centeredSaddlePhase] using hs'

end ZudilinZeta
end
end

-- Component: missions.zudilin.Params13GammaAmplitude
section
set_option autoImplicit false
noncomputable section
open Complex Filter Topology MeasureTheory Set

namespace ZudilinZeta
open GammaEstimates

lemma norm_complex_nat_inv_le_one (n : ℕ) : ‖(n : ℂ)⁻¹‖ ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [norm_inv, Complex.norm_natCast]
    apply inv_le_one_of_one_le₀
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn

lemma continuous_params13GammaCorrection_vertical (n : ℕ) (τ : ℂ)
    (hτ : 87 ≤ τ.re ∧ τ.re ≤ 175 / 2) :
    Continuous (fun t : ℝ => params13GammaCorrection n (τ + (t : ℂ) * I)) := by
  by_cases hn : n = 0
  · subst n
    simp only [params13GammaCorrection, Nat.cast_zero, zero_mul]
    exact continuous_const
  rw [continuous_iff_continuousAt]
  intro t
  apply tendsto_finsetProd
  intro i hi
  have hb := params13GammaBase_re_ge_one
    (z := τ + (t : ℂ) * I) (by simpa using hτ) i hi
  have hp : 0 < ((n : ℂ) * params13GammaBase (τ + (t : ℂ) * I) i).re := by
    simpa using mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn) : (0 : ℝ) < n)
      (show 0 < (params13GammaBase (τ + (t : ℂ) * I) i).re by linarith)
  have hin : Continuous (fun t : ℝ => (n : ℂ) * params13GammaBase (τ + (t : ℂ) * I) i) := by
    exact continuous_const.mul ((continuous_params13GammaBase i).comp (by fun_prop))
  exact ((hasDerivAt_normalizedGamma hp).continuousAt.comp
    (f := fun t : ℝ => (n : ℂ) * params13GammaBase (τ + (t : ℂ) * I) i)
    hin.continuousAt).zpow₀
    (params13GammaWeight i) (Or.inl (normalizedGamma_ne_zero hp))

lemma continuous_params13GammaAmplitude_vertical (n : ℕ) (τ : ℂ)
    (hτ : 87 ≤ τ.re ∧ τ.re ≤ 175 / 2) :
    Continuous (fun t : ℝ => params13GammaAmplitude n (τ + (t : ℂ) * I)) := by
  have hin : Continuous (fun t : ℝ => τ + (t : ℂ) * I) := by fun_prop
  have hs : Continuous (fun t : ℝ => params13GammaShift (n : ℂ)⁻¹ (τ + (t : ℂ) * I)) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (continuousAt_params13GammaShift (n : ℂ)⁻¹ (τ + (t : ℂ) * I)
      (by simpa using hτ) ((Complex.re_le_norm _).trans (norm_complex_nat_inv_le_one n))).comp
        (f := fun t : ℝ => ((n : ℂ)⁻¹, τ + (t : ℂ) * I))
        (continuous_const.prodMk hin).continuousAt
  have hl : Continuous (fun t : ℝ => params13GammaLeading (τ + (t : ℂ) * I)) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (continuousAt_params13GammaLeading _ (by simpa using hτ)).comp hin.continuousAt
  exact (hs.mul hl).mul (continuous_params13GammaCorrection_vertical n τ hτ)

lemma norm_params13GammaAmplitude_le (n : ℕ) (hn : 8 ≤ n) (z : ℂ)
    (hz : 87 ≤ z.re ∧ z.re ≤ 175 / 2) :
    ‖params13GammaAmplitude n z‖ ≤
      (2 * ‖params13GammaShiftConstant‖ * (2 : ℝ) ^ 48) * (‖z‖ + 100) ^ 55 := by
  have hs := norm_params13GammaShift_le (n : ℂ)⁻¹ z hz (norm_complex_nat_inv_le_one n)
  have hl := norm_params13GammaLeading_le z hz
  have hg := norm_params13GammaCorrection_le n hn z hz
  unfold params13GammaAmplitude
  rw [norm_mul, norm_mul]
  calc
    _ ≤ (2 * (‖z‖ + 100) ^ 7 * ‖params13GammaShiftConstant‖) *
        (‖z‖ + 100) ^ 48 * (2 : ℝ) ^ 48 := by gcongr
    _ = _ := by ring

lemma params13GammaAmplitude_polynomial_bound (τ : ℂ)
    (hτ : 87 ≤ τ.re ∧ τ.re ≤ 175 / 2) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ n : ℕ, 8 ≤ n → ∀ t : ℝ,
      ‖params13GammaAmplitude n (τ + (t : ℂ) * I)‖ ≤ A * (1 + |t|) ^ 55 := by
  let D := 2 * ‖params13GammaShiftConstant‖ * (2 : ℝ) ^ 48
  refine ⟨D * (‖τ‖ + 100) ^ 55, by dsimp [D]; positivity, ?_⟩
  intro n hn t
  have hb := norm_params13GammaAmplitude_le n hn (τ + (t : ℂ) * I) (by simpa using hτ)
  have hz : ‖τ + (t : ℂ) * I‖ ≤ ‖τ‖ + |t| := by
    simpa only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      using norm_add_le τ ((t : ℂ) * I)
  have hK : ‖τ + (t : ℂ) * I‖ + 100 ≤ (‖τ‖ + 100) * (1 + |t|) := by
    nlinarith [abs_nonneg t, mul_nonneg (norm_nonneg τ) (abs_nonneg t)]
  calc
    _ ≤ D * (‖τ + (t : ℂ) * I‖ + 100) ^ 55 := hb
    _ ≤ D * ((‖τ‖ + 100) * (1 + |t|)) ^ 55 := by
      apply mul_le_mul_of_nonneg_left _ (by dsimp [D]; positivity)
      exact pow_le_pow_left₀ (by positivity) hK 55
    _ = _ := by rw [mul_pow]; dsimp [D]; ring

lemma params13_gamma_amplitude_saddle_limit (τ : ℂ)
    (hroot : charPoly params13 τ = 0) (him : 0 < τ.im)
    (hmax : ∀ σ : ℂ, charPoly params13 σ = 0 → 0 < σ.im → σ.re ≤ τ.re) :
    Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ) : ℂ) * ∫ t : ℝ,
      params13GammaAmplitude n (τ + (t : ℂ) * I) * Complex.exp ((n : ℂ) *
        (adjustedSaddlePhase params13 (τ + (t : ℂ) * I) - f0 params13 τ))) atTop
      (𝓝 (params13GammaLimitAmplitude τ *
        ((Real.pi : ℂ) / (saddlePhaseSecond params13 τ / 2)) ^ (1 / 2 : ℂ))) := by
  obtain ⟨hx, _⟩ := saddle_params13_maximal_root_box τ hroot him hmax
  have hτ : 87 ≤ τ.re ∧ τ.re ≤ 175 / 2 :=
    ⟨by linarith only [hx.1], by linarith only [hx.2]⟩
  obtain ⟨A, hA, hbound⟩ := params13GammaAmplitude_polynomial_bound τ hτ
  apply params13_full_saddle_asymptotic τ hroot him hmax
    (fun n t => params13GammaAmplitude n (τ + (t : ℂ) * I))
    (params13GammaLimitAmplitude τ) A 55 hA
  · exact fun n => (continuous_params13GammaAmplitude_vertical n τ hτ).measurable
  · intro u
    have hs : Tendsto (fun n : ℕ => u / Real.sqrt (n : ℝ)) atTop (𝓝 0) :=
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_div_atTop u
    apply tendsto_params13GammaAmplitude_moving _ hτ
    simpa only [Complex.ofReal_zero, zero_mul, add_zero] using (hs.ofReal.mul_const I).const_add τ
  · filter_upwards [eventually_ge_atTop (8 : ℕ)] with n hn
    exact hbound n hn

end ZudilinZeta
end
end

-- Component: missions.zudilin.Params13GammaKernel
section
set_option autoImplicit false
noncomputable section
open Complex Filter Topology

namespace ZudilinZeta
open GammaEstimates

lemma params13GammaShiftIndex_small (i : ℕ) :
    params13GammaShiftIndex i = -1 ∨ params13GammaShiftIndex i = 0 ∨
      params13GammaShiftIndex i = 1 ∨ params13GammaShiftIndex i = 2 := by
  unfold params13GammaShiftIndex
  split_ifs <;> simp

lemma params13GammaShiftIndex_weight_sum :
    ∑ i ∈ Finset.range 39, params13GammaShiftIndex i * params13GammaWeight i = -3 := by
  norm_num [params13GammaShiftIndex, params13GammaWeight, Finset.sum_range_succ]

lemma params13_scaled_shift_product (h z : ℂ) :
    (91 - 2 * z + 2 * h) *
      (∏ i ∈ Finset.range 39,
        gammaScaledShiftFactor h (params13GammaBase z i) (params13GammaShiftIndex i) ^
          params13GammaWeight i) = params13GammaShift h z := by
  norm_num [params13GammaShiftIndex, params13GammaWeight, params13GammaBase,
    params13GammaSlope, params13GammaOffset, gammaScaledShiftFactor,
    params13GammaShift, params13GammaShiftConstant, eta13, Finset.prod_range_succ,
    Finset.prod_Icc_succ_top]
  ring

lemma params13GammaKernel_exact (n : ℕ) (hn : 2 ≤ n) (z : ℂ)
    (hz : 87 ≤ z.re ∧ z.re ≤ 175 / 2) :
    params13GammaKernel n z = ((2 * (Real.pi : ℂ)) ^ 5 / (n : ℂ) ^ 7) *
      Complex.exp ((n : ℂ) * saddlePhase params13 z) * params13GammaAmplitude n z := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hline : 91 * (n : ℂ) + 2 - 2 * (n : ℂ) * z =
      (n : ℂ) * (91 - 2 * z + 2 * (n : ℂ)⁻¹) := by
    field_simp <;> ring
  have halgebra (L B S : ℂ) :
      ((n : ℂ) * L) * (B * (n : ℂ) ^ (-3 : ℤ) * S) =
        (n : ℂ) ^ (-2 : ℤ) * B * (L * S) := by
    simp only [zpow_neg, zpow_ofNat]
    field_simp <;> ring
  unfold params13GammaKernel
  rw [gamma_small_shift_product (Finset.range 39) (params13GammaBase z)
    params13GammaWeight params13GammaShiftIndex n hn (params13GammaBase_re_ge_one hz)
    (fun i _ => params13GammaShiftIndex_small i),
    params13GammaShiftIndex_weight_sum, hline, halgebra, params13_scaled_shift_product,
    params13_bare_gamma_product n (by omega) z hz]
  unfold params13GammaAmplitude
  simp only [zpow_neg, zpow_ofNat]
  field_simp <;> ring

end ZudilinZeta
end
end

-- Component: missions.zudilin.Params13KernelAsymptotic
section
set_option autoImplicit false
noncomputable section
open Complex Filter Topology MeasureTheory

namespace ZudilinZeta

def params13SaddleCoefficient (τ : ℂ) : ℂ :=
  params13GammaLimitAmplitude τ *
    ((Real.pi : ℂ) / (saddlePhaseSecond params13 τ / 2)) ^ (1 / 2 : ℂ)

lemma params13KernelIntegral_normalization (n : ℕ) (hn : 2 ≤ n) (τ : ℂ)
    (hτ : 87 ≤ τ.re ∧ τ.re ≤ 175 / 2) :
    ((n : ℂ) ^ 7 * (Real.sqrt (n : ℝ) : ℂ) / (2 * (Real.pi : ℂ)) ^ 5) *
      Complex.exp (-(n : ℂ) * f0 params13 τ) * params13KernelIntegral n τ =
    (Real.sqrt (n : ℝ) : ℂ) * ∫ t : ℝ,
      params13GammaAmplitude n (τ + (t : ℂ) * I) * Complex.exp ((n : ℂ) *
        (adjustedSaddlePhase params13 (τ + (t : ℂ) * I) - f0 params13 τ)) := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hpoint (t : ℝ) :
      params13GammaKernel n (τ + (t : ℂ) * I) *
        Complex.exp (-(n : ℂ) * (Real.pi : ℂ) * I * (τ + (t : ℂ) * I)) =
      (((2 * (Real.pi : ℂ)) ^ 5 / (n : ℂ) ^ 7) * Complex.exp ((n : ℂ) * f0 params13 τ)) *
        (params13GammaAmplitude n (τ + (t : ℂ) * I) * Complex.exp ((n : ℂ) *
          (adjustedSaddlePhase params13 (τ + (t : ℂ) * I) - f0 params13 τ))) := by
    rw [params13GammaKernel_exact n hn _ (by simpa using hτ)]
    have he : Complex.exp ((n : ℂ) * saddlePhase params13 (τ + (t : ℂ) * I)) *
        Complex.exp (-(n : ℂ) * (Real.pi : ℂ) * I * (τ + (t : ℂ) * I)) =
      Complex.exp ((n : ℂ) * f0 params13 τ) * Complex.exp ((n : ℂ) *
        (adjustedSaddlePhase params13 (τ + (t : ℂ) * I) - f0 params13 τ)) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      unfold adjustedSaddlePhase
      ring
    calc
      _ = ((2 * (Real.pi : ℂ)) ^ 5 / (n : ℂ) ^ 7) *
          (Complex.exp ((n : ℂ) * saddlePhase params13 (τ + (t : ℂ) * I)) *
            Complex.exp (-(n : ℂ) * (Real.pi : ℂ) * I * (τ + (t : ℂ) * I))) *
          params13GammaAmplitude n (τ + (t : ℂ) * I) := by ring
      _ = _ := by rw [he]; ring
  unfold params13KernelIntegral
  rw [integral_congr_ae (ae_of_all _ hpoint), integral_const_mul]
  have he : Complex.exp (-(n : ℂ) * f0 params13 τ) *
      Complex.exp ((n : ℂ) * f0 params13 τ) = 1 := by
    rw [← Complex.exp_add, show -(n : ℂ) * f0 params13 τ + (n : ℂ) * f0 params13 τ = 0 by ring,
      Complex.exp_zero]
  have hscale : (((n : ℂ) ^ 7 * (Real.sqrt (n : ℝ) : ℂ) / (2 * (Real.pi : ℂ)) ^ 5) *
      ((2 * (Real.pi : ℂ)) ^ 5 / (n : ℂ) ^ 7)) = (Real.sqrt (n : ℝ) : ℂ) := by
    field_simp [hn0, hp]
  calc
    _ = (((n : ℂ) ^ 7 * (Real.sqrt (n : ℝ) : ℂ) / (2 * (Real.pi : ℂ)) ^ 5) *
        ((2 * (Real.pi : ℂ)) ^ 5 / (n : ℂ) ^ 7)) *
        (Complex.exp (-(n : ℂ) * f0 params13 τ) * Complex.exp ((n : ℂ) * f0 params13 τ)) *
        (∫ t : ℝ, params13GammaAmplitude n (τ + (t : ℂ) * I) * Complex.exp ((n : ℂ) *
          (adjustedSaddlePhase params13 (τ + (t : ℂ) * I) - f0 params13 τ))) := by ring
    _ = _ := by rw [he, hscale, mul_one]

lemma params13_kernel_saddle_asymptotic (τ : ℂ)
    (hroot : charPoly params13 τ = 0) (him : 0 < τ.im)
    (hmax : ∀ σ : ℂ, charPoly params13 σ = 0 → 0 < σ.im → σ.re ≤ τ.re) :
    Tendsto (fun n : ℕ =>
      ((n : ℂ) ^ 7 * (Real.sqrt (n : ℝ) : ℂ) / (2 * (Real.pi : ℂ)) ^ 5) *
        Complex.exp (-(n : ℂ) * f0 params13 τ) * params13KernelIntegral n τ)
      atTop (𝓝 (params13SaddleCoefficient τ)) := by
  obtain ⟨hx, _⟩ := saddle_params13_maximal_root_box τ hroot him hmax
  have hτ : 87 ≤ τ.re ∧ τ.re ≤ 175 / 2 :=
    ⟨by linarith only [hx.1], by linarith only [hx.2]⟩
  apply (params13_gamma_amplitude_saddle_limit τ hroot him hmax).congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  exact (params13KernelIntegral_normalization n hn τ hτ).symm

lemma params13SaddleCoefficient_ne_zero (τ : ℂ)
    (hroot : charPoly params13 τ = 0) (him : 0 < τ.im)
    (hmax : ∀ σ : ℂ, charPoly params13 σ = 0 → 0 < σ.im → σ.re ≤ τ.re) :
    params13SaddleCoefficient τ ≠ 0 := by
  obtain ⟨hx, hy⟩ := saddle_params13_maximal_root_box τ hroot him hmax
  have hτ : 87 ≤ τ.re ∧ τ.re ≤ 175 / 2 :=
    ⟨by linarith only [hx.1], by linarith only [hx.2]⟩
  have hs := saddlePhaseSecond_params13_re_pos τ hτ
    (by rw [abs_of_pos him]; linarith only [hy.2])
  have hb : 0 < (saddlePhaseSecond params13 τ / 2).re := by simpa using half_pos hs
  have hg := saddle_gaussian_integral_nonzero τ hroot him hmax
  rw [integral_gaussian_complex hb] at hg
  exact mul_ne_zero (params13GammaLimitAmplitude_ne_zero τ hτ) hg

end ZudilinZeta
end
end

theorem solution (τ : ℂ)
    (hroot : ZudilinZeta.charPoly ZudilinZeta.params13 τ = 0) (him : 0 < τ.im)
    (hmax : ∀ σ : ℂ, ZudilinZeta.charPoly ZudilinZeta.params13 σ = 0 →
      0 < σ.im → σ.re ≤ τ.re) :
    (87 ≤ τ.re ∧ τ.re ≤ 175 / 2) ∧ ∃ c : ℂ, c ≠ 0 ∧
      Filter.Tendsto (fun n : ℕ =>
        ((n : ℂ) ^ 7 * (Real.sqrt (n : ℝ) : ℂ) / (2 * (Real.pi : ℂ)) ^ 5) *
          Complex.exp (-(n : ℂ) * ZudilinZeta.f0 ZudilinZeta.params13 τ) *
            ZudilinZeta.params13KernelIntegral n τ) Filter.atTop (nhds c) := by
  obtain ⟨hx, _⟩ := ZudilinZeta.saddle_params13_maximal_root_box τ hroot him hmax
  exact ⟨⟨by linarith only [hx.1], by linarith only [hx.2]⟩,
    ZudilinZeta.params13SaddleCoefficient τ,
    ZudilinZeta.params13SaddleCoefficient_ne_zero τ hroot him hmax,
    ZudilinZeta.params13_kernel_saddle_asymptotic τ hroot him hmax⟩
