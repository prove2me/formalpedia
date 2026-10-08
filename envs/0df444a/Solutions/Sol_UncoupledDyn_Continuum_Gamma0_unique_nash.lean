-- Prove2me | solution 1 for UncoupledDyn.Continuum.Gamma0_unique_nash
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T07:50:07.968291+00:00
-- url     : https://prove2.me/submissions/65480c26-c978-4296-b776-71a1ad4a4be1

import Mathlib
import Definitions.Def_UncoupledDyn_Continuum_Setting
open UncoupledDyn.Continuum
set_option maxHeartbeats 800000

private noncomputable def R : ℂ :=
  Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)
private noncomputable def c (z : ℂ) : ℂ :=
  let t := max ‖z‖ (1/3 : ℝ)
  (((1-t)/t : ℝ) : ℂ) + (((3*t-1)/(2*t) : ℝ) : ℂ) * R

private theorem phi_formula (z : ℂ) : phi z = c z * z := by
  unfold phi c
  split_ifs with h
  · rw [max_eq_right h]
    norm_num
  · rw [max_eq_left (le_of_not_ge h)]
    unfold R
    ring

private theorem rotation_norm : ‖R‖ = 1 := by
  simp [R, Complex.norm_exp]

private theorem rotation_parts : 0 < R.re ∧ 0 < R.im := by
  have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  simp only [R, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Real.cos_pi_div_four, Real.sin_pi_div_four]
  constructor <;> linarith

private theorem coefficient_parts (z : ℂ) (hz : z ∈ D) :
    0 < (c z).re ∧ 0 ≤ (c z).im ∧ (1/3 < ‖z‖ → 0 < (c z).im) := by
  have hr : ‖z‖ ≤ 1 := by simpa [D, Metric.mem_closedBall, dist_zero_right] using hz
  have ht0 : 0 < max ‖z‖ (1/3 : ℝ) := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have ht1 : max ‖z‖ (1/3 : ℝ) ≤ 1 := max_le hr (by norm_num)
  have ha : 0 ≤ (1-max ‖z‖ (1/3 : ℝ))/max ‖z‖ (1/3 : ℝ) :=
    div_nonneg (by linarith) ht0.le
  have hb : 0 ≤ (3*max ‖z‖ (1/3 : ℝ)-1)/(2*max ‖z‖ (1/3 : ℝ)) :=
    div_nonneg (by linarith [le_max_right ‖z‖ (1/3 : ℝ)]) (by positivity)
  have hbreal : 0 < (c z).re := by
    by_cases hh : max ‖z‖ (1/3 : ℝ) = 1/3
    · dsimp only [c]
      rw [hh]
      norm_num
    · have hbp : 0 < (3*max ‖z‖ (1/3 : ℝ)-1)/(2*max ‖z‖ (1/3 : ℝ)) :=
        div_pos (by
          have ht : 1/3 < max ‖z‖ (1/3 : ℝ) :=
            lt_of_le_of_ne (le_max_right _ _) (Ne.symm hh)
          linarith) (by positivity)
      dsimp only [c]
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      exact add_pos_of_nonneg_of_pos ha (mul_pos hbp rotation_parts.1)
  refine ⟨hbreal, ?_, ?_⟩
  · dsimp only [c]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, zero_add]
    exact mul_nonneg hb rotation_parts.2.le
  · intro hout
    have hbp : 0 < (3*max ‖z‖ (1/3 : ℝ)-1)/(2*max ‖z‖ (1/3 : ℝ)) :=
      div_pos (by linarith [le_max_left ‖z‖ (1/3 : ℝ)]) (by positivity)
    dsimp only [c]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, zero_add]
    exact mul_pos hbp rotation_parts.2

private theorem phi_maps : Set.MapsTo phi D D := by
  intro z hz
  have hr : ‖z‖ ≤ 1 := by simpa [D, Metric.mem_closedBall, dist_zero_right] using hz
  apply (show phi z ∈ D ↔ ‖phi z‖ ≤ 1 by
    simp [D, Metric.mem_closedBall, dist_zero_right]).mpr
  by_cases hh : ‖z‖ ≤ 1/3
  · rw [phi, if_pos hh, norm_mul]
    norm_num [Complex.norm_ofNat]
    linarith
  · have hr0 : 0 < ‖z‖ := by linarith [norm_nonneg z]
    have ha : 0 ≤ (1-‖z‖)/‖z‖ := div_nonneg (by linarith) hr0.le
    have hb : 0 ≤ (3*‖z‖-1)/(2*‖z‖) := div_nonneg (by linarith) (by positivity)
    rw [phi, if_neg hh]
    calc
      ‖(((1-‖z‖)/‖z‖ : ℝ) : ℂ)*z +
          (((3*‖z‖-1)/(2*‖z‖) : ℝ) : ℂ)*(R*z)‖
          ≤ (1-‖z‖)/‖z‖*‖z‖ + (3*‖z‖-1)/(2*‖z‖)*‖z‖ := by
        calc
          _ ≤ ‖(((1-‖z‖)/‖z‖ : ℝ) : ℂ)*z‖ +
            ‖(((3*‖z‖-1)/(2*‖z‖) : ℝ) : ℂ)*(R*z)‖ := norm_add_le _ _
          _ = _ := by
            simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg ha, abs_of_nonneg hb, rotation_norm, one_mul]
      _ = (1+‖z‖)/2 := by field_simp; ring
      _ ≤ 1 := by linarith

private theorem phi_cont : Continuous phi := by
  have ht : Continuous (fun z : ℂ => max ‖z‖ (1/3 : ℝ)) := continuous_norm.max continuous_const
  have htne (z : ℂ) : max ‖z‖ (1/3 : ℝ) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num) (le_max_right _ _))
  have hA : Continuous (fun z : ℂ => (1-max ‖z‖ (1/3 : ℝ))/max ‖z‖ (1/3 : ℝ)) :=
    (continuous_const.sub ht).div ht htne
  have hB : Continuous (fun z : ℂ => (3*max ‖z‖ (1/3 : ℝ)-1)/(2*max ‖z‖ (1/3 : ℝ))) :=
    ((continuous_const.mul ht).sub continuous_const).div (continuous_const.mul ht)
      (fun z => mul_ne_zero (by norm_num) (htne z))
  have hc : Continuous c :=
    (Complex.continuous_ofReal.comp hA).add ((Complex.continuous_ofReal.comp hB).mul continuous_const)
  have he : phi = fun z => c z*z := funext phi_formula
  rw [he]
  simpa only [Pi.mul_def, id_def] using hc.mul continuous_id

private theorem phi_no_cycle (z : ℂ) (hz : z ∈ D) (hne : z ≠ 0) : phi (phi z) ≠ z := by
  intro he
  have hw := phi_maps hz
  have hp := coefficient_parts z hz
  have hq := coefficient_parts (phi z) hw
  have hprod : c (phi z)*c z = 1 := by
    apply mul_right_cancel₀ hne
    simpa only [phi_formula, mul_assoc, one_mul] using he
  by_cases hsmall : ‖z‖ ≤ 1/3
  · by_cases hsmall' : ‖phi z‖ ≤ 1/3
    · have h1 : phi z = 2*z := by rw [phi, if_pos hsmall]
      have h2 : phi (phi z) = 2*phi z := by rw [phi, if_pos hsmall']
      rw [h2, h1] at he
      have : z = 0 := by linear_combination (1/3 : ℂ)*he
      exact hne this
    · have him := congrArg Complex.im hprod
      simp only [Complex.mul_im, Complex.one_im] at him
      nlinarith [mul_nonneg hq.1.le hp.2.1, mul_pos (hq.2.2 (lt_of_not_ge hsmall')) hp.1]
  · have him := congrArg Complex.im hprod
    simp only [Complex.mul_im, Complex.one_im] at him
    nlinarith [mul_pos hq.1 (hp.2.2 (lt_of_not_ge hsmall)), mul_nonneg hq.2.1 hp.1.le]

private theorem phi_zero : phi 0 = 0 := by norm_num [phi]

private theorem gamma_mem : Gamma0 ∈ U0 := by
  refine ⟨fun _ => phi, (fun _ => ⟨phi_cont.continuousOn, phi_maps⟩), ?_, ?_⟩
  · intro i
    refine ⟨0, ⟨by simp [D], by simp [phi_zero]⟩, ?_⟩
    intro z hz
    by_contra hne
    exact phi_no_cycle z hz.1 hne hz.2
  · intro i x hx
    rfl

private theorem gamma_nash (x : Fin 2 → ℂ) : IsNash Gamma0 x ↔ x = 0 := by
  constructor
  · intro hn
    have hx (i : Fin 2) : x i ∈ D := hn.1 i (Set.mem_univ _)
    have hb (i : Fin 2) : x i = phi (x (i+1)) := by
      have hh := hn.2 i (phi (x (i+1))) (phi_maps (hx (i+1)))
      have hni : i+1 ≠ i := by fin_cases i <;> decide
      simp only [Gamma0, Function.update_self, Function.update_of_ne hni, sub_self,
        norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, neg_zero] at hh
      have he : ‖x i - phi (x (i+1))‖ = 0 := by
        nlinarith [norm_nonneg (x i - phi (x (i+1)))]
      exact sub_eq_zero.mp (norm_eq_zero.mp he)
    have hz (i : Fin 2) : x i = 0 := by
      by_contra hne
      have hcy : phi (phi (x i)) = x i := by
        have hi : i+1+1 = i := by fin_cases i <;> decide
        have hh := hb (i+1)
        rw [hi] at hh
        rw [← hh, ← hb i]
      exact phi_no_cycle (x i) (hx i) hne hcy
    funext i
    exact hz i
  · intro he
    subst x
    refine ⟨?_, ?_⟩
    · intro i hi
      simp [D]
    · intro i z hz
      have hni : i+1 ≠ i := by fin_cases i <;> decide
      simp only [Gamma0, Function.update_self, Function.update_of_ne hni, Pi.zero_apply,
        phi_zero, sub_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, neg_zero]
      exact neg_nonpos.mpr (sq_nonneg ‖z‖)

theorem solution : Gamma0 ∈ U0 ∧ ∀ x, IsNash Gamma0 x ↔ x = 0 := by
  exact ⟨gamma_mem, gamma_nash⟩

#print axioms solution
