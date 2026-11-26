-- Prove2me | solution 1 for Section5BooleanFrame.tilted_covariance
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:09:25.031209+00:00
-- url     : https://prove2.me/submissions/8b8bcc43-0bc1-4109-a4f1-2addd3805dfa

import Definitions.Def_Section5Verified_Section5BooleanFrameCovariance
import Definitions.Def_Section5Verified_Section5BooleanFrameMoments
import Mathlib
import Theorems.Thm_Section5BooleanFrame_sign_fourth
set_option autoImplicit false
namespace Section5BooleanFrame
end Section5BooleanFrame
open Section5BooleanFrame
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem solution (w : ι → ℝ) (i j : ι) :
    Section5BooleanFrame.average (fun x => Section5BooleanFrame.amplitude w x ^ 2*(Section5BooleanFrame.sign x i*Section5BooleanFrame.sign x j))=
      (if i=j then ∑ k, w k ^ 2 else 0)+2*w i*w j-
        (if i=j then 2*w i ^ 2 else 0) := by
  have hexp (x : ι → Bool) :
      Section5BooleanFrame.amplitude w x ^ 2*(Section5BooleanFrame.sign x i*Section5BooleanFrame.sign x j)=
        ∑ k, ∑ l, (w k*w l)*(Section5BooleanFrame.sign x k*Section5BooleanFrame.sign x l*Section5BooleanFrame.sign x i*Section5BooleanFrame.sign x j) := by
    rw [Section5BooleanFrame.amplitude_sq_expansion]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  simp only [hexp,Section5BooleanFrame.average_sum,Section5BooleanFrame.average_smul,Section5BooleanFrame.sign_fourth]
  by_cases hij : i=j
  · subst j
    simp [Finset.sum_add_distrib,Finset.sum_sub_distrib,mul_add,mul_sub,
      Finset.mul_sum,Finset.sum_mul,mul_ite,ite_mul,pow_two]
    ring
  · simp [hij,Ne.symm hij,Finset.sum_add_distrib,Finset.sum_sub_distrib,
      mul_add,mul_sub,Finset.mul_sum,Finset.sum_mul,mul_ite,ite_mul]
    ring
