-- Prove2me | solution 2 for Psi.numNBeforeDD_fUD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:47:33.607336+00:00
-- url     : https://prove2.me/submissions/3778a56f-5e5f-4295-ae88-8aa6b4f3be1c

import Definitions.Def_RequestProject_Psi_Inverse
import Definitions.Def_RequestProject_Psi_Bijection

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (m : ℕ) :
    numNBeforeDD ((List.replicate m [true, false]).flatten) = m := by
  induction m with
  | zero => simp [numNBeforeDD]
  | succ k ih =>
    have hstep : (List.replicate (k+1) [true, false]).flatten
        = true :: false :: (List.replicate k [true, false]).flatten := by
      rw [List.replicate_succ, List.flatten_cons]; rfl
    rw [hstep]
    cases k with
    | zero => rfl
    | succ j =>
      have hstep2 : (List.replicate (j+1) [true, false]).flatten
          = true :: false :: (List.replicate j [true, false]).flatten := by
        rw [List.replicate_succ, List.flatten_cons]; rfl
      show numNBeforeDD (true :: false :: (List.replicate (j+1) [true, false]).flatten) = j + 1 + 1
      rw [hstep2]
      show numNBeforeDD (false :: true :: false :: (List.replicate j [true, false]).flatten) + 1
          = j + 1 + 1
      have hrfl : numNBeforeDD (false :: true :: false :: (List.replicate j [true, false]).flatten)
          = numNBeforeDD (true :: false :: (List.replicate j [true, false]).flatten) := rfl
      rw [hrfl, ← hstep2, ih]
end Psi
