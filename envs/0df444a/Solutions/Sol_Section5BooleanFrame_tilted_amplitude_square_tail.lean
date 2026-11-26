-- Prove2me | solution 1 for Section5BooleanFrame.tilted_amplitude_square_tail
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:54:51.567625+00:00
-- url     : https://prove2.me/submissions/7a14fdd7-4f6d-46ce-ae3a-9ab6738ce689

import Definitions.Def_Section5Verified_Section5BooleanFrameCovariance
import Definitions.Def_Section5Verified_Section5BooleanFrameMoments
import Definitions.Def_Section5Verified_Section5TiltedFrameTail
import Mathlib
import Theorems.Thm_Section5BooleanFrame_amplitude_absolute_tail
import Theorems.Thm_Section5BooleanFrame_amplitude_fourth
section
set_option autoImplicit false

namespace Section5BooleanFrame

variable {ι : Type*} [Fintype ι] [DecidableEq ι]



theorem amplitude_fourth_le (w : ι → ℝ) (hw : ∑ i, w i^2=1) :
    average (fun x => amplitude w x^4) ≤ 3 := by
  rw [amplitude_fourth,hw]
  have he : 0 ≤ ∑ i, w i^4 := Finset.sum_nonneg (fun i _ => by positivity)
  linarith

end Section5BooleanFrame

end
section
set_option autoImplicit false

namespace Section5BooleanFrame

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem average_nonneg (f : (ι → Bool) → ℝ) (h : ∀ x, 0 ≤ f x) : 0 ≤ average f := by
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg (fun x _ => h x))



theorem average_cauchy_schwarz (f g : (ι → Bool) → ℝ) :
    average (fun x => f x*g x)^2 ≤ average (fun x => f x^2)*average (fun x => g x^2) := by
  have he := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  unfold average
  calc
    _ = (Fintype.card (ι → Bool) : ℝ)⁻¹^2*(∑ x, f x*g x)^2 := by ring
    _ ≤ (Fintype.card (ι → Bool) : ℝ)⁻¹^2*((∑ x, f x^2)*(∑ x, g x^2)) :=
      mul_le_mul_of_nonneg_left he (sq_nonneg _)
    _ = _ := by ring



end Section5BooleanFrame

end
section
set_option autoImplicit false

namespace Section5BooleanFrame

variable {ι : Type*} [Fintype ι] [DecidableEq ι]



theorem tiltedMean_eq (w : ι → ℝ) (f : (ι → Bool) → ℝ) :
    tiltedMean w f=average (fun x => amplitude w x^2*f x) := by
  simp only [tiltedMean,weight,average,Finset.mul_sum,mul_assoc]



theorem tiltedMean_indicator_sq_le (w : ι → ℝ) (hw : ∑ i, w i^2=1)
    (P : (ι → Bool) → Prop) [DecidablePred P] :
    tiltedMean w (fun x => if P x then 1 else 0)^2 ≤
      3*average (fun x => if P x then 1 else 0) := by
  rw [tiltedMean_eq]
  have hcs := average_cauchy_schwarz (fun x => amplitude w x^2)
    (fun x => if P x then (1 : ℝ) else 0)
  have hpow (x : ι → Bool) : (amplitude w x^2)^2=amplitude w x^4 := by ring
  have hind (x : ι → Bool) : (if P x then (1 : ℝ) else 0)^2=
      if P x then 1 else 0 := by split <;> norm_num
  simp only [hpow,hind] at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_right (amplitude_fourth_le w hw)
    (average_nonneg _ (fun x => by split <;> norm_num)))

theorem tilted_amplitude_absolute_tail (w u : ι → ℝ) (hw : ∑ i, w i^2=1)
    (hu : ∑ i, u i^2=1) (r : ℝ) (hr : 0 ≤ r) :
    tiltedMean w (fun x => if r ≤ |amplitude u x| then 1 else 0) ≤
      3*Real.exp (-r^2/4) := by
  have hsq := tiltedMean_indicator_sq_le w hw (fun x => r ≤ |amplitude u x|)
  have ht := amplitude_absolute_tail u hu r hr
  have he : Real.exp (-r^2/4)^2=Real.exp (-r^2/2) := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  have hp := Real.exp_pos (-r^2/4)
  nlinarith [Real.exp_pos (-r^2/2)]



end Section5BooleanFrame

end
set_option autoImplicit false
namespace Section5BooleanFrame
end Section5BooleanFrame
open Section5BooleanFrame
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem solution (w u : ι → ℝ) (hw : ∑ i, w i^2=1)
    (hu : ∑ i, u i^2=1) (t : ℝ) (ht : 0 ≤ t) :
    Section5BooleanFrame.tiltedMean w (fun x => if t ≤ Section5BooleanFrame.amplitude u x^2 then 1 else 0) ≤
      3*Real.exp (-t/4) := by
  have he (x : ι → Bool) : t ≤ Section5BooleanFrame.amplitude u x^2 ↔ Real.sqrt t ≤ |Section5BooleanFrame.amplitude u x| := by
    have hs := Real.sq_sqrt ht
    have ha := sq_abs (Section5BooleanFrame.amplitude u x)
    constructor <;> intro h
    · nlinarith [Real.sqrt_nonneg t,abs_nonneg (Section5BooleanFrame.amplitude u x)]
    · nlinarith [Real.sqrt_nonneg t,abs_nonneg (Section5BooleanFrame.amplitude u x)]
  simp only [he]
  simpa only [Real.sq_sqrt ht] using
    Section5BooleanFrame.tilted_amplitude_absolute_tail w u hw hu (Real.sqrt t) (Real.sqrt_nonneg t)
