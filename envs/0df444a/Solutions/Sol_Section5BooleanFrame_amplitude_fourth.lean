-- Prove2me | solution 1 for Section5BooleanFrame.amplitude_fourth
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:10:51.298182+00:00
-- url     : https://prove2.me/submissions/3269b3c0-20c7-4d71-89f7-5e5c226d8f3f

import Definitions.Def_Section5Verified_Section5BooleanFrameCovariance
import Definitions.Def_Section5Verified_Section5BooleanFrameMoments
import Mathlib
import Theorems.Thm_Section5BooleanFrame_tilted_covariance
set_option autoImplicit false
namespace Section5BooleanFrame
end Section5BooleanFrame
open Section5BooleanFrame
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem solution (w : ι → ℝ) :
    Section5BooleanFrame.average (fun x => Section5BooleanFrame.amplitude w x^4)=3*(∑ i, w i^2)^2-2*(∑ i, w i^4) := by
  have hexp (x : ι → Bool) : Section5BooleanFrame.amplitude w x^4=
      ∑ i, ∑ j, (w i*w j)*(Section5BooleanFrame.amplitude w x^2*(Section5BooleanFrame.sign x i*Section5BooleanFrame.sign x j)) := by
    have he := Section5BooleanFrame.amplitude_sq_expansion w x
    calc
      _ = Section5BooleanFrame.amplitude w x^2*Section5BooleanFrame.amplitude w x^2 := by ring
      _ = Section5BooleanFrame.amplitude w x^2*(∑ i, ∑ j, (w i*w j)*(Section5BooleanFrame.sign x i*Section5BooleanFrame.sign x j)) :=
        congrArg (fun a => Section5BooleanFrame.amplitude w x^2*a) he
      _ = _ := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
  simp only [hexp,Section5BooleanFrame.average_sum,Section5BooleanFrame.average_smul,Section5BooleanFrame.tilted_covariance]
  simp only [mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib,mul_ite,mul_zero]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
  have hdiag : (∑ i, w i*w i*(∑ k, w k^2))=(∑ k, w k^2)^2 := by
    simp only [← pow_two,← Finset.sum_mul,pow_two]
  have houter : (∑ i, ∑ j, w i*w j*(2*w i*w j))=2*(∑ i, w i^2)^2 := by
    have he (i j : ι) : w i*w j*(2*w i*w j)=2*(w i^2*w j^2) := by ring
    simp only [he,← Finset.mul_sum,← Finset.sum_mul,pow_two]
  have hlast : (∑ i, w i*w i*(2*w i^2))=2*(∑ i, w i^4) := by
    have he (i : ι) : w i*w i*(2*w i^2)=2*w i^4 := by ring
    simp only [he,Finset.mul_sum]
  rw [hdiag,houter,hlast]
  ring
