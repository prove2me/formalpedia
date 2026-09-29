-- Prove2me | solution 1 for WorkbookCorrected.plus_13466
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T14:01:21.090652+00:00
-- url     : https://prove2.me/submissions/cdf8f6de-b8ad-44d2-adfc-42830543dabf

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
private lemma tangent (a : ℝ) (ha : 0<a) : 23-81/(a^2+2) ≤ 2*Real.sqrt 7*a := by
  have hs : (Real.sqrt 7)^2=7 := Real.sq_sqrt (by norm_num)
  have hd : 0<a^2+2 := by positivity
  have hp : 0 ≤ (a-Real.sqrt 7)^2*(2*Real.sqrt 7*a+5) := by positivity
  have hi : (2*Real.sqrt 7*a-23)*(a^2+2)+81 = (a-Real.sqrt 7)^2*(2*Real.sqrt 7*a+5) := by
    nlinarith only [hs,congrArg (fun x : ℝ => x*a^2) hs,congrArg (fun x : ℝ => x*(Real.sqrt 7)*a) hs]
  have he : 81/(a^2+2)*(a^2+2)=81 := div_mul_cancel₀ _ (ne_of_gt hd)
  have hm : 0 ≤ (2*Real.sqrt 7*a-(23-81/(a^2+2)))*(a^2+2) := by nlinarith only [hi,hp,he]
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_right hd).mp hm)
theorem solution (a b c : ℝ) (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (h : 1/(a^2+2)+1/(b^2+2)+1/(c^2+2)=1/3) : a+b+c ≥ 3*Real.sqrt 7 := by
  have hsum : 81/(a^2+2)+81/(b^2+2)+81/(c^2+2)=27 := by
    have hh := congrArg (fun x : ℝ => 81*x) h
    convert hh using 1 <;> ring
  have hh := tangent a ha
  have hi := tangent b hb
  have hj := tangent c hc
  have hs : (Real.sqrt 7)^2=7 := Real.sq_sqrt (by norm_num)
  have hp : 0<Real.sqrt 7 := by positivity
  nlinarith only [hsum,hh,hi,hj,hs,hp]
example : (∀ (a b c : ℝ) (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (h : 1/(a^2+2)+1/(b^2+2)+1/(c^2+2)=1/3), a+b+c ≥ 3*Real.sqrt 7) := @solution
#print axioms solution
