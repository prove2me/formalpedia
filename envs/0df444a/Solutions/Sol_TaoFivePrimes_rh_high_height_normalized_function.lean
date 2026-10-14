-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_normalized_function
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-14T09:47:14.684023+00:00
-- url     : https://prove2.me/submissions/1c24cb99-850c-4158-a351-0691d3662769

import Definitions.Def_TaoFivePrimes_RHHighHeightWindow
import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RHHighHeightProof
open Complex Set MeasureTheory HurwitzZeta
open scoped ComplexConjugate
noncomputable def P : WeakFEPair ℂ := hurwitzEvenFEPair 0
lemma kernel_conj {t : ℝ} (ht : 0<t) : conj (P.f_modif t)=P.f_modif t := by
  rcases lt_trichotomy t 1 with h | rfl | h
  · have he : P.f_modif t = (evenKernel 0 t : ℂ) -
        ((t^(-(1:ℝ)/2):ℝ):ℂ) := by
      simp [P,WeakFEPair.f_modif,hurwitzEvenFEPair,ht,h,not_lt.mpr h.le]
      norm_num
    rw [he]
    simp
  · simp [P,WeakFEPair.f_modif]
  · have he : P.f_modif t = (evenKernel 0 t : ℂ)-1 := by
      simp [P,WeakFEPair.f_modif,hurwitzEvenFEPair,ht,h,not_lt.mpr h.le]
    rw [he]
    simp
lemma entire_completed_conj (s : ℂ) :
    completedRiemannZeta₀ (conj s)=conj (completedRiemannZeta₀ s) := by
  change mellin P.f_modif (conj s/2)/2 = conj (mellin P.f_modif (s/2)/2)
  rw [map_div₀,map_ofNat]
  congr 1
  rw [mellin,mellin,←integral_conj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have ht0 : 0<t := ht
  have ha : (t:ℂ).arg≠Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg ht0.le]
    exact ne_of_lt Real.pi_pos
  have he : conj s/2-1=conj (s/2-1) := by simp only [map_sub,map_div₀,map_one,map_ofNat]
  dsimp only
  rw [he,Complex.cpow_conj _ _ ha]
  simp only [smul_eq_mul,map_mul,conj_ofReal,kernel_conj ht0]
lemma completed_conj (s : ℂ) :
    completedRiemannZeta (conj s)=conj (completedRiemannZeta s) := by
  simp only [completedRiemannZeta_eq,entire_completed_conj,map_sub,map_div₀,map_one]
lemma critical_ne_zero (t : ℝ) : RHHighHeight.critical t≠0 := by
  intro h
  have := congrArg Complex.re h
  norm_num [RHHighHeight.critical] at this
lemma critical_ne_one (t : ℝ) : RHHighHeight.critical t≠1 := by
  intro h
  have := congrArg Complex.re h
  norm_num [RHHighHeight.critical] at this
lemma critical_re (t : ℝ) : (RHHighHeight.critical t).re=1/2 := by
  simp [RHHighHeight.critical]
lemma completed_critical_real (t : ℝ) :
    (completedRiemannZeta (RHHighHeight.critical t)).im=0 := by
  have hc : conj (RHHighHeight.critical t)=1-RHHighHeight.critical t := by
    apply Complex.ext <;> simp [RHHighHeight.critical]
    ring
  have he := completed_conj (RHHighHeight.critical t)
  rw [hc,completedRiemannZeta_one_sub] at he
  have hi := congrArg Complex.im he
  simp only [conj_im] at hi
  linarith
lemma normalized_real (t : ℝ) : (RHHighHeight.normalizedComplex t).im=0 := by
  simp only [RHHighHeight.normalizedComplex,mul_im,ofReal_re,ofReal_im,completed_critical_real,mul_zero,zero_mul,add_zero]
lemma normalized_zero_iff (t : ℝ) :
    RHHighHeight.normalized t=0 ↔ riemannZeta (RHHighHeight.critical t)=0 := by
  have hg : Gammaℝ (RHHighHeight.critical t)≠0 :=
    Gammaℝ_ne_zero_of_re_pos (by rw [critical_re]; norm_num)
  have hz : RHHighHeight.normalized t=0 ↔ RHHighHeight.normalizedComplex t=0 := by
    constructor
    · intro h; exact Complex.ext h (normalized_real t)
    · intro h; simpa [RHHighHeight.normalized] using congrArg Complex.re h
  rw [hz,RHHighHeight.normalizedComplex,mul_eq_zero]
  simp only [ofReal_eq_zero,Real.exp_ne_zero,false_or]
  rw [riemannZeta_def_of_ne_zero (critical_ne_zero t),div_eq_zero_iff]
  simp [hg]
lemma normalized_continuous : Continuous RHHighHeight.normalized := by
  have hc : Continuous RHHighHeight.critical := by unfold RHHighHeight.critical; fun_prop
  have hΛ : Continuous (fun t : ℝ => completedRiemannZeta (RHHighHeight.critical t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (differentiableAt_completedZeta (critical_ne_zero t) (critical_ne_one t)).continuousAt.comp hc.continuousAt
  unfold RHHighHeight.normalized RHHighHeight.normalizedComplex
  exact Complex.continuous_re.comp ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp (by fun_prop))).mul hΛ)
end RHHighHeightProof

theorem solution :
    (∀ t : ℝ, (RHHighHeight.normalizedComplex t).im=0) ∧
    Continuous RHHighHeight.normalized ∧
    (∀ t : ℝ, RHHighHeight.normalized t=0 ↔ riemannZeta (RHHighHeight.critical t)=0) :=
  ⟨RHHighHeightProof.normalized_real,RHHighHeightProof.normalized_continuous,
    RHHighHeightProof.normalized_zero_iff⟩
