-- Prove2me | solution 1 for Section5BooleanFrame.amplitude_absolute_tail
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:51:38.420705+00:00
-- url     : https://prove2.me/submissions/5e8c69bc-004d-4669-bca4-c53c18078b09

import Definitions.Def_Section5Verified_Section5BooleanFrameCovariance
import Definitions.Def_Section5Verified_Section5BooleanFrameMoments
import Mathlib
import Theorems.Thm_Section5BooleanFrame_amplitude_mgf_le
section
set_option autoImplicit false

/-! Exact moments of the full Boolean sign frame. These are concrete finite
sums, with no independence or moment assumptions. They identify the covariance
that a coded, bounded-independence implementation must reproduce. -/

namespace Section5BooleanFrame

variable {ι : Type*} [Fintype ι] [DecidableEq ι]















theorem average_add (f g : (ι → Bool) → ℝ) :
    average (fun x => f x+g x)=average f+average g := by
  simp [average,Finset.sum_add_distrib,mul_add]

















end Section5BooleanFrame

end
section
set_option autoImplicit false

namespace Section5BooleanFrame

variable {ι : Type*} [Fintype ι] [DecidableEq ι]



theorem average_mono (f g : (ι → Bool) → ℝ) (h : ∀ x, f x ≤ g x) : average f ≤ average g := by
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun x _ => h x))
    (inv_nonneg.mpr (Nat.cast_nonneg _))



theorem average_exponential_markov (f : (ι → Bool) → ℝ) (r t : ℝ) (ht : 0 ≤ t) :
    average (fun x => if r ≤ f x then 1 else 0) ≤
      Real.exp (-t*r)*average (fun x => Real.exp (t*f x)) := by
  rw [← average_smul]
  apply average_mono
  intro x
  rw [← Real.exp_add]
  by_cases hx : r ≤ f x
  · rw [if_pos hx]
    apply Real.one_le_exp_iff.mpr
    nlinarith [mul_nonneg ht (sub_nonneg.mpr hx)]
  · rw [if_neg hx]
    exact (Real.exp_pos _).le

end Section5BooleanFrame

end
section
set_option autoImplicit false

namespace Section5BooleanFrame

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem amplitude_upper_tail (u : ι → ℝ) (hu : ∑ i, u i^2=1) (r : ℝ) (hr : 0 ≤ r) :
    average (fun x => if r ≤ amplitude u x then 1 else 0) ≤ Real.exp (-r^2/2) := by
  calc
    _ ≤ Real.exp (-r*r)*average (fun x => Real.exp (r*amplitude u x)) :=
      average_exponential_markov _ r r hr
    _ ≤ Real.exp (-r*r)*Real.exp (r^2*(∑ i, u i^2)/2) :=
      mul_le_mul_of_nonneg_left (amplitude_mgf_le u r) (Real.exp_pos _).le
    _ = _ := by rw [hu,← Real.exp_add]; congr 1; ring

theorem amplitude_lower_tail (u : ι → ℝ) (hu : ∑ i, u i^2=1) (r : ℝ) (hr : 0 ≤ r) :
    average (fun x => if r ≤ -amplitude u x then 1 else 0) ≤ Real.exp (-r^2/2) := by
  have he : (∑ i, (-u i)^2)=1 := by simpa using hu
  have hn (x : ι → Bool) : amplitude (fun i => -u i) x= -amplitude u x := by
    simp [amplitude,Finset.sum_neg_distrib]
  simpa only [hn] using amplitude_upper_tail (fun i => -u i) he r hr



end Section5BooleanFrame

end
set_option autoImplicit false
namespace Section5BooleanFrame
end Section5BooleanFrame
open Section5BooleanFrame
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem solution (u : ι → ℝ) (hu : ∑ i, u i^2=1) (r : ℝ) (hr : 0 ≤ r) :
    Section5BooleanFrame.average (fun x => if r ≤ |Section5BooleanFrame.amplitude u x| then 1 else 0) ≤ 2*Real.exp (-r^2/2) := by
  have he : Section5BooleanFrame.average (fun x => if r ≤ |Section5BooleanFrame.amplitude u x| then 1 else 0) ≤
      Section5BooleanFrame.average (fun x => if r ≤ Section5BooleanFrame.amplitude u x then 1 else 0)+
        Section5BooleanFrame.average (fun x => if r ≤ -Section5BooleanFrame.amplitude u x then 1 else 0) := by
    rw [← Section5BooleanFrame.average_add]
    apply Section5BooleanFrame.average_mono
    intro x
    by_cases hpos : 0 ≤ Section5BooleanFrame.amplitude u x
    · rw [abs_of_nonneg hpos]
      split <;> split <;> norm_num
    · rw [abs_of_neg (lt_of_not_ge hpos)]
      split <;> split <;> norm_num
  linarith [Section5BooleanFrame.amplitude_upper_tail u hu r hr,Section5BooleanFrame.amplitude_lower_tail u hu r hr]
