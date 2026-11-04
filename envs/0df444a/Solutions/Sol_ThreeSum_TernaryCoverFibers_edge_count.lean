-- Prove2me | solution 1 for ThreeSum.TernaryCoverFibers.edge_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:45:19.673556+00:00
-- url     : https://prove2.me/submissions/0d9ac79f-c2d0-4cf4-92bd-af7708056482

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_TernaryCoverFibers

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverFibers
open Finset
open scoped BigOperators
variable {E Q K : Type*} [Fintype E] [Fintype Q] [Fintype K]
variable [DecidableEq Q] [DecidableEq K] [AddCommGroup K]
namespace ThreeSum.TernaryCoverFibers
theorem _root_.solution (output : E → Q) (G : ℕ)
    (hfiber : ∀ q : Q, (univ.filter fun e => output e = q).card = G) :
    Fintype.card E = Fintype.card Q * G := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (univ : Finset E)) (t := (univ : Finset Q)) (f := output)
    (fun _ _ => mem_univ _)
  simpa [hfiber] using h
end ThreeSum.TernaryCoverFibers
