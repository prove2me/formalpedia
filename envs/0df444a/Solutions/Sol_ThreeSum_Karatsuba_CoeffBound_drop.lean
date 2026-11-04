-- Prove2me | solution 1 for ThreeSum.Karatsuba.CoeffBound.drop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:41:35.704087+00:00
-- url     : https://prove2.me/submissions/be2ede52-5bd4-4f62-8e2a-1032230e173e

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
    CoeffBound (as.drop n) U :=
  .of_mem (coeffBound_nonneg h) (fun x hx => h.mem (List.mem_of_mem_drop hx))
end CoeffBound
end ThreeSum.Karatsuba
