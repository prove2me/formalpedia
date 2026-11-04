-- Prove2me | solution 1 for ThreeSum.HashFamily.incidenceCount_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:04:26.720827+00:00
-- url     : https://prove2.me/submissions/45dae517-dc0a-44e7-a2bc-500bb2602e5b

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_ThreeSum_HashFamily

set_option autoImplicit false
open ThreeSum ThreeSum.HashFamily
open scoped BigOperators
variable {α K : Type*}
variable {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq Ω]
namespace ThreeSum.HashFamily
theorem _root_.solution {events events' : E → Finset Ω}
    (h : ∀ e, events e ⊆ events' e) (w : Ω) :
    incidenceCount events w ≤ incidenceCount events' w := by
  apply Finset.card_le_card
  intro e he
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, h e (Finset.mem_filter.mp he).2⟩
end ThreeSum.HashFamily
