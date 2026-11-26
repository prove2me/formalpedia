-- Prove2me | solution 1 for Section5BooleanFrame.sign_fourth
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:08:02.671803+00:00
-- url     : https://prove2.me/submissions/0aa5f0f5-ac36-43db-83a2-3e26e0cdeb82

import Definitions.Def_Section5Verified_Section5BooleanFrameMoments
import Mathlib
set_option autoImplicit false
namespace Section5BooleanFrame
end Section5BooleanFrame
open Section5BooleanFrame
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem solution (i j k l : ι) :
    Section5BooleanFrame.average (fun x : ι → Bool => Section5BooleanFrame.sign x i*Section5BooleanFrame.sign x j*Section5BooleanFrame.sign x k*Section5BooleanFrame.sign x l)=
      (if i=j then 1 else 0)*(if k=l then 1 else 0)+
      (if i=k then 1 else 0)*(if j=l then 1 else 0)+
      (if i=l then 1 else 0)*(if j=k then 1 else 0)-
      2*(if i=j then 1 else 0)*(if i=k then 1 else 0)*(if i=l then 1 else 0) := by
  by_cases hij : i=j
  · subst j
    simp only [Section5BooleanFrame.sign_mul_self,one_mul,Section5BooleanFrame.sign_second]
    by_cases hik : i=k <;> by_cases hil : i=l <;> simp_all <;> norm_num
  · by_cases hik : i=k
    · subst k
      have he (x : ι → Bool) : Section5BooleanFrame.sign x i*Section5BooleanFrame.sign x j*Section5BooleanFrame.sign x i*Section5BooleanFrame.sign x l=Section5BooleanFrame.sign x j*Section5BooleanFrame.sign x l := by
        calc
          _ = (Section5BooleanFrame.sign x i*Section5BooleanFrame.sign x i)*(Section5BooleanFrame.sign x j*Section5BooleanFrame.sign x l) := by ring
          _ = _ := by rw [Section5BooleanFrame.sign_mul_self,one_mul]
      simp only [he,Section5BooleanFrame.sign_second]
      by_cases hil : i=l <;> by_cases hjl : j=l <;> simp_all
    · by_cases hil : i=l
      · subst l
        have he (x : ι → Bool) : Section5BooleanFrame.sign x i*Section5BooleanFrame.sign x j*Section5BooleanFrame.sign x k*Section5BooleanFrame.sign x i=Section5BooleanFrame.sign x j*Section5BooleanFrame.sign x k := by
          calc
            _ = (Section5BooleanFrame.sign x i*Section5BooleanFrame.sign x i)*(Section5BooleanFrame.sign x j*Section5BooleanFrame.sign x k) := by ring
            _ = _ := by rw [Section5BooleanFrame.sign_mul_self,one_mul]
        simp [he,Section5BooleanFrame.sign_second,hij,hik]
      · have hz : Section5BooleanFrame.average (fun x : ι → Bool => Section5BooleanFrame.sign x i*Section5BooleanFrame.sign x j*Section5BooleanFrame.sign x k*Section5BooleanFrame.sign x l)=0 := by
          apply Section5BooleanFrame.average_zero_of_flip i
          intro x
          rw [Section5BooleanFrame.sign_flip_same,Section5BooleanFrame.sign_flip_other x (Ne.symm hij),
            Section5BooleanFrame.sign_flip_other x (Ne.symm hik),Section5BooleanFrame.sign_flip_other x (Ne.symm hil)]
          ring
        simp [hz,hij,hik,hil]
