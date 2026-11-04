-- Prove2me | solution 1 for ThreeSum.Reporting.generated_candidates_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:23:30.303178+00:00
-- url     : https://prove2.me/submissions/58a7b9f1-7ce7-417f-99ed-804468a6dd2c

import Definitions.Def_Submission_ThreeSum_Subset
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Card
import Definitions.Def_Submission_ThreeSum_Reporting

set_option autoImplicit false
open ThreeSum ThreeSum.Reporting
open Finset
open scoped BigOperators
variable {ι α : Type*} [DecidableEq α]
namespace ThreeSum.Reporting
theorem _root_.solution (parents : List (List α)) (children : List α) :
    (parents.flatMap fun pre => children.map fun x => pre ++ [x]).length =
      parents.length * children.length := by
  induction parents with
  | nil => simp
  | cons pre parents ih => simp [ih, Nat.add_mul, Nat.add_comm]
end ThreeSum.Reporting
