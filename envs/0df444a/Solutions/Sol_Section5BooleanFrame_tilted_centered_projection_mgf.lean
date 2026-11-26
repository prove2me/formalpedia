-- Prove2me | solution 1 for Section5BooleanFrame.tilted_centered_projection_mgf
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:07:46.230514+00:00
-- url     : https://prove2.me/submissions/df21b3d5-e3aa-44ed-be09-3f6feb7a7e16

import Definitions.Def_Section5Verified_Section5BooleanFrameCovariance
import Definitions.Def_Section5Verified_Section5BooleanFrameMoments
import Definitions.Def_Section5Verified_Section5FiniteProbabilityLaw
import Definitions.Def_Section5Verified_Section5TiltedFrameTail
import Definitions.Def_Section5Verified_Section5TiltedProjectionMGF
import Mathlib
import Theorems.Thm_Section5BernsteinFoundation_hdpc_subE_mgf
import Theorems.Thm_Section5BooleanFrame_amplitude_fourth
import Theorems.Thm_Section5BooleanFrame_tilted_amplitude_square_tail
import Theorems.Thm_Section5FiniteProbability_exponential_moment_of_tail
import Theorems.Thm_Section5FiniteProbability_law_integral
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

/-! Finite real probability weights as an actual probability measure, with
exact finite-sum integral and event-probability formulas. -/

namespace Section5FiniteProbability

open MeasureTheory

variable {Ω : Type*} [Fintype Ω]



@[simp] theorem mass_apply (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x=1) (x : Ω) :
    mass p hp hs x=ENNReal.ofReal (p x) := rfl







theorem law_event [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x=1)
    (P : Ω → Prop) [DecidablePred P] :
    (law p hp hs).real {x | P x}=∑ x, if P x then p x else 0 := by
  classical
  rw [measureReal_def,law,PMF.toMeasure_apply_fintype]
  rw [ENNReal.toReal_sum (fun x _ => by by_cases h : P x <;> simp [h])]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : P x <;> simp [h,hp x]

end Section5FiniteProbability

end
section
set_option autoImplicit false

namespace Section5BooleanFrame

variable {ι : Type*} [Fintype ι] [DecidableEq ι]



theorem tiltedMean_eq (w : ι → ℝ) (f : (ι → Bool) → ℝ) :
    tiltedMean w f=average (fun x => amplitude w x^2*f x) := by
  simp only [tiltedMean,weight,average,Finset.mul_sum,mul_assoc]









end Section5BooleanFrame

end
section
set_option autoImplicit false

namespace Section5BooleanFrame

open MeasureTheory ProbabilityTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace (ι → Bool)] [MeasurableSingletonClass (ι → Bool)]





theorem probabilityLaw_integral (w : ι → ℝ) (hw : ∑ i, w i^2=1) (f : (ι → Bool) → ℝ) :
    (∫ x, f x ∂probabilityLaw w hw)=tiltedMean w f :=
  Section5FiniteProbability.law_integral _ _ _ _

theorem probabilityLaw_event (w : ι → ℝ) (hw : ∑ i, w i^2=1)
    (P : (ι → Bool) → Prop) [DecidablePred P] :
    (probabilityLaw w hw).real {x | P x}=tiltedMean w (fun x => if P x then 1 else 0) := by
  rw [probabilityLaw,Section5FiniteProbability.law_event]
  simp only [tiltedMean,mul_ite,mul_one,mul_zero]

theorem tilted_projection_second (w u : ι → ℝ) (hw : ∑ i, w i^2=1)
    (hu : ∑ i, u i^2=1) : tiltedMean w (fun x => amplitude u x^2) ≤ 3 := by
  have hcs := average_cauchy_schwarz (fun x => amplitude w x^2) (fun x => amplitude u x^2)
  have he (a : ℝ) : (a^2)^2=a^4 := by ring
  simp only [he] at hcs
  have hprod : average (fun x => amplitude w x^4)*average (fun x => amplitude u x^4) ≤ 3*3 :=
    mul_le_mul (amplitude_fourth_le w hw) (amplitude_fourth_le u hu)
      (average_nonneg _ (fun x => by positivity)) (by norm_num)
  rw [tiltedMean_eq]
  nlinarith

theorem tilted_projection_exponential (w u : ι → ℝ) (hw : ∑ i, w i^2=1)
    (hu : ∑ i, u i^2=1) :
    (∫ x, Real.exp (amplitude u x^2/512) ∂probabilityLaw w hw) ≤ 130/127 := by
  apply Section5FiniteProbability.exponential_moment_of_tail
  · intro x
    exact sq_nonneg _
  · intro t ht
    rw [probabilityLaw_event]
    exact tilted_amplitude_square_tail w u hw hu t ht

theorem tilted_centered_projection_exponential (w u : ι → ℝ) (hw : ∑ i, w i^2=1)
    (hu : ∑ i, u i^2=1) :
    (∫ x, Real.exp (|amplitude u x^2-
      (∫ y, amplitude u y^2 ∂probabilityLaw w hw)|/512) ∂probabilityLaw w hw) ≤ 2 := by
  let m := ∫ y, amplitude u y^2 ∂probabilityLaw w hw
  have hm0 : 0 ≤ m := integral_nonneg (fun y => sq_nonneg _)
  have hm3 : m ≤ 3 := by
    rw [show m=tiltedMean w (fun y => amplitude u y^2) from probabilityLaw_integral w hw _]
    exact tilted_projection_second w u hw hu
  have hpt (x : ι → Bool) : Real.exp (|amplitude u x^2-m|/512) ≤
      Real.exp (3/512)*Real.exp (amplitude u x^2/512) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have ha : |amplitude u x^2-m| ≤ amplitude u x^2+3 := by
      apply abs_le.mpr
      constructor <;> nlinarith [sq_nonneg (amplitude u x)]
    linarith
  have hsmall : Real.exp (3/512 : ℝ) ≤ 512/509 := by
    convert Real.exp_bound_div_one_sub_of_interval (by norm_num : (0 : ℝ) ≤ 3/512)
      (by norm_num : (3/512 : ℝ) < 1) using 1 <;> norm_num
  calc
    _ ≤ ∫ x, Real.exp (3/512)*Real.exp (amplitude u x^2/512) ∂probabilityLaw w hw :=
      integral_mono (Integrable.of_finite) (Integrable.of_finite) hpt
    _ = Real.exp (3/512)*(∫ x, Real.exp (amplitude u x^2/512) ∂probabilityLaw w hw) :=
      integral_const_mul _ _
    _ ≤ (512/509)*(130/127) :=
      mul_le_mul hsmall (tilted_projection_exponential w u hw hu)
        (integral_nonneg (fun x => (Real.exp_pos _).le)) (by norm_num)
    _ ≤ 2 := by norm_num



end Section5BooleanFrame

end
set_option autoImplicit false
namespace Section5BooleanFrame
end Section5BooleanFrame
open Section5BooleanFrame
open MeasureTheory ProbabilityTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace (ι → Bool)] [MeasurableSingletonClass (ι → Bool)]
theorem solution (w u : ι → ℝ) (hw : ∑ i, w i^2=1)
    (hu : ∑ i, u i^2=1) (l : ℝ) (hl : |l| *512 ≤ 1/2) :
    mgf (fun x => Section5BooleanFrame.amplitude u x^2-(∫ y, Section5BooleanFrame.amplitude u y^2 ∂Section5BooleanFrame.probabilityLaw w hw))
      (Section5BooleanFrame.probabilityLaw w hw) l ≤ Real.exp (32*l^2*512^2) := by
  have hmean : (∫ x, (Section5BooleanFrame.amplitude u x^2-
      (∫ y, Section5BooleanFrame.amplitude u y^2 ∂Section5BooleanFrame.probabilityLaw w hw)) ∂Section5BooleanFrame.probabilityLaw w hw)=0 := by
    rw [integral_sub (Integrable.of_finite) (integrable_const _),integral_const]
    simp
  exact (Section5BernsteinFoundation.hdpc_subE_mgf (Section5BooleanFrame.probabilityLaw w hw) _
    (measurable_of_finite _) hmean 512 (by norm_num) (Integrable.of_finite)
    (Section5BooleanFrame.tilted_centered_projection_exponential w u hw hu) l hl).2
