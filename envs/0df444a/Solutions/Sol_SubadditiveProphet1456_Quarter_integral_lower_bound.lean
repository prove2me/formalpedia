-- Prove2me | solution 1 for SubadditiveProphet1456.Quarter.integral_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T01:12:22.625131+00:00
-- url     : https://prove2.me/submissions/635f4366-1832-471a-8ace-0010ab56001f

import Definitions.Def_SubadditiveProphet1456_Quarter_CapHeight
import Definitions.Def_SubadditiveProphet1456_Quarter_Machine

open scoped BigOperators NNReal ENNReal
open MeasureTheory
open SubadditiveProphet1456.Quarter

namespace IntegralLowerBoundAux

lemma R_pos {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    0 < (1+t)*Real.exp (-2*t) - (1-t) := by
  have hx : 0 < 2*t/(1-t) := div_pos (by linarith) (by linarith)
  have h := Real.lt_log_one_add_of_pos hx
  have hne : (1 - t) ≠ 0 := (by linarith : (0:ℝ) < 1 - t).ne'
  have e1 : 2 * (2*t/(1-t)) / (2*t/(1-t) + 2) = 2*t := by
    field_simp
    ring
  have e2 : 1 + 2*t/(1-t) = (1+t)/(1-t) := by
    field_simp
    ring
  rw [e1, e2] at h
  have hpos : 0 < (1+t)/(1-t) := div_pos (by linarith) (by linarith)
  have h3 : Real.exp (2*t) < (1+t)/(1-t) := by
    calc Real.exp (2*t) < Real.exp (Real.log ((1+t)/(1-t))) := Real.exp_lt_exp.mpr h
      _ = (1+t)/(1-t) := Real.exp_log hpos
  have h4 : Real.exp (2*t) * (1-t) < 1+t := (lt_div_iff₀ (by linarith)).mp h3
  have h5 : Real.exp (2*t) * Real.exp (-2*t) = 1 := by
    rw [← Real.exp_add]
    have : 2*t + -2*t = 0 := by ring
    rw [this, Real.exp_zero]
  have h6 : Real.exp (2*t) * (1-t) * Real.exp (-2*t) < (1+t) * Real.exp (-2*t) :=
    mul_lt_mul_of_pos_right h4 (Real.exp_pos _)
  have h7 : Real.exp (2*t) * (1-t) * Real.exp (-2*t) = 1 - t := by
    rw [mul_right_comm, h5, one_mul]
  linarith

lemma R_nonneg {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    0 ≤ (1+t)*Real.exp (-2*t) - (1-t) := by
  rcases h0.eq_or_lt with h | h
  · subst h
    simp
  · rcases h1.eq_or_lt with h' | h'
    · subst h'
      have := Real.exp_pos (-2*1 : ℝ)
      linarith
    · exact (R_pos h h').le

noncomputable def Q (s x : ℝ) : ℝ := -(1+x) + (1-s)*x*(1+s*x)

noncomputable def Psi (s x : ℝ) : ℝ := (1-x) * Q s x * J s x

noncomputable def dPsi (s t : ℝ) : ℝ :=
  ((-(Q s t) + (1-t)*(-1 + (1-s)*(1+2*s*t)))
    - ((1-t)*(Q s t))*(s^2 + s*Real.exp (-2*t))) * J s t

lemma hasDerivAt_J (s t : ℝ) :
    HasDerivAt (fun x => J s x) (J s t * (-(s^2 + s*Real.exp (-2*t)))) t := by
  have hid := hasDerivAt_id' t
  have hE : HasDerivAt (fun x : ℝ => Real.exp (-2*x)) (Real.exp (-2*t) * (-2*1)) t :=
    (hid.const_mul (-2:ℝ)).exp
  have h := ((hid.const_mul (-s^2)).sub ((hE.const_sub 1).const_mul (s/2))).exp
  unfold J
  refine h.congr_deriv ?_
  simp only [Pi.sub_apply]
  ring

lemma hasDerivAt_Psi (s t : ℝ) : HasDerivAt (fun x => Psi s x) (dPsi s t) t := by
  have hid := hasDerivAt_id' t
  have h1 : HasDerivAt (fun x : ℝ => 1 - x) (-1) t := hid.const_sub 1
  have hQ : HasDerivAt (fun x : ℝ => Q s x) (-1 + (1-s)*(1+2*s*t)) t := by
    have h := ((hid.const_add 1).neg).add
      ((hid.const_mul (1-s)).mul ((hid.const_mul s).const_add 1))
    unfold Q
    refine h.congr_deriv ?_
    ring
  have h := (h1.mul hQ).mul (hasDerivAt_J s t)
  unfold Psi dPsi
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply]
  ring

lemma cont_J (s : ℝ) : Continuous (fun t => J s t) := by
  unfold J
  fun_prop

lemma cont_dPsi (s : ℝ) : Continuous (fun t => dPsi s t) := by
  unfold dPsi Q J
  fun_prop

lemma integral_dPsi (s : ℝ) : ∫ t in (0:ℝ)..1, dPsi s t = 1 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => Psi s x)
    (fun t _ => hasDerivAt_Psi s t) ((cont_dPsi s).intervalIntegrable 0 1)]
  simp [Psi, Q, J]

lemma pointwise {s t : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    s * Real.exp (-(3:ℝ)/2) * ((1-t)^2 * ((1+t)*Real.exp (-2*t) - (1-t)))
      ≤ dPsi s t - (1+s^2) * J s t := by
  have hE0 : 0 < Real.exp (-2*t) := Real.exp_pos _
  have hE1 : Real.exp (-2*t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hR : 0 ≤ (1+t)*Real.exp (-2*t) - (1-t) := R_nonneg ht0 ht1
  have hs' : 0 ≤ 1 - s := by linarith
  have ht' : 0 ≤ 1 - t := by linarith
  have hc0 : 0 < Real.exp (-(3:ℝ)/2) := Real.exp_pos _
  have hJ : Real.exp (-(3:ℝ)/2) ≤ J s t := by
    unfold J
    apply Real.exp_le_exp.mpr
    have hs2 : s^2 ≤ 1 := by nlinarith
    have a1 : s^2 * t ≤ 1 := by
      nlinarith [mul_le_mul hs2 ht1 ht0 (by norm_num : (0:ℝ) ≤ 1)]
    have a2 : s * (1 - Real.exp (-2*t)) ≤ 1 := by
      nlinarith [mul_le_mul hs1 (by linarith : 1 - Real.exp (-2*t) ≤ 1)
        (by linarith : 0 ≤ 1 - Real.exp (-2*t)) (by norm_num : (0:ℝ) ≤ 1)]
    nlinarith
  have hJpos : 0 < J s t := lt_of_lt_of_le hc0 hJ
  have key : dPsi s t - (1+s^2) * J s t =
      s*(1-t)*((1+t)*Real.exp (-2*t) - (1-t))*((1-t*(1-s))*J s t)
      + (1-s)*t*(1-t)*s*((1+t)*(1-s) + t*(1-s)*(s+Real.exp (-2*t)))*J s t := by
    unfold dPsi Q
    ring
  have hbr : 0 ≤ (1+t)*(1-s) + t*(1-s)*(s+Real.exp (-2*t)) :=
    add_nonneg (mul_nonneg (by linarith) hs')
      (mul_nonneg (mul_nonneg ht0 hs') (by linarith))
  have hb : 0 ≤ (1-s)*t*(1-t)*s*((1+t)*(1-s) + t*(1-s)*(s+Real.exp (-2*t)))*J s t :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hs' ht0) ht') hs0.le) hbr)
      hJpos.le
  have ha : (1-t)*Real.exp (-(3:ℝ)/2) ≤ (1-t*(1-s))*J s t := by
    have h1 := mul_le_mul_of_nonneg_left hJ ht'
    have h2 : 0 ≤ t*s*J s t := mul_nonneg (mul_nonneg ht0 hs0.le) hJpos.le
    nlinarith
  have hm := mul_le_mul_of_nonneg_left ha
    (show 0 ≤ s*(1-t)*((1+t)*Real.exp (-2*t) - (1-t)) from
      mul_nonneg (mul_nonneg hs0.le ht') hR)
  rw [key]
  nlinarith

end IntegralLowerBoundAux

open IntegralLowerBoundAux in
theorem solution :
    0 < tailConstant ∧ ∀ s : ℝ, 0 < s → s ≤ 1 → 2*tailConstant*s ≤ F s := by
  have hRc : Continuous (fun t : ℝ => (1-t)^2 * ((1+t)*Real.exp (-2*t) - (1-t))) := by
    fun_prop
  constructor
  · unfold tailConstant
    apply mul_pos (by positivity)
    apply intervalIntegral.intervalIntegral_pos_of_pos_on (hRc.intervalIntegrable 0 1)
    · intro t ht
      exact mul_pos (pow_pos (by linarith [ht.2]) 2) (R_pos ht.1 ht.2)
    · norm_num
  · intro s hs0 hs1
    have hJi : IntervalIntegrable (fun t => J s t) volume 0 1 :=
      (cont_J s).intervalIntegrable 0 1
    have hdi : IntervalIntegrable (fun t => dPsi s t) volume 0 1 :=
      (cont_dPsi s).intervalIntegrable 0 1
    have hF : F s = ∫ t in (0:ℝ)..1, (dPsi s t - (1+s^2) * J s t) := by
      rw [intervalIntegral.integral_sub hdi (hJi.const_mul (1+s^2)),
        intervalIntegral.integral_const_mul, integral_dPsi]
      rfl
    have hc : 2*tailConstant*s = ∫ t in (0:ℝ)..1,
        s * Real.exp (-(3:ℝ)/2) * ((1-t)^2 * ((1+t)*Real.exp (-2*t) - (1-t))) := by
      rw [intervalIntegral.integral_const_mul]
      unfold tailConstant
      ring
    rw [hF, hc]
    apply intervalIntegral.integral_mono_on zero_le_one
      ((continuous_const.mul hRc).intervalIntegrable 0 1) (hdi.sub (hJi.const_mul (1+s^2)))
    intro t ht
    exact pointwise hs0 hs1 ht.1 ht.2
