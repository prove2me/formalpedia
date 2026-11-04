-- Prove2me | solution 1 for ThreeSum.Karatsuba.CoeffBound.take
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:41:34.509633+00:00
-- url     : https://prove2.me/submissions/77741de6-e6ae-4e5e-bcf3-2d9d9470304e

import Definitions.Def_Submission_ThreeSum_Karatsuba
import Mathlib.Data.List.GetD
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Theorems.Thm_ThreeSum_Karatsuba_coeffBound_nonneg
import Theorems.Thm_ThreeSum_Karatsuba_CoeffBound_of_mem
import Theorems.Thm_ThreeSum_Karatsuba_CoeffBound_mem

set_option autoImplicit false
open ThreeSum ThreeSum.Karatsuba
open Polynomial
open scoped BigOperators
namespace ThreeSum.Karatsuba
namespace CoeffBound
theorem _root_.solution {as : List ℤ} {U : ℤ} (h : CoeffBound as U) (n : ℕ) :
    CoeffBound (as.take n) U :=
  .of_mem (coeffBound_nonneg h) (fun x hx => h.mem (List.mem_of_mem_take hx))
end CoeffBound
end ThreeSum.Karatsuba
