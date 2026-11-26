-- Prove2me | solution 1 for Sabidussi.LoopMultigraph.EulerTour.degree_eq_two_mul_card_occurrence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:14:24.926175+00:00
-- url     : https://prove2.me/submissions/3d6a8b0a-a189-4397-bc27-b6734a6f935a

import Definitions.Def_Sabidussi_Color
import Definitions.Def_Sabidussi_Statement
import Mathlib.Data.Fin.Rev
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finite.Set
import Mathlib.Data.Fintype.Sets
import Definitions.Def_Sabidussi_LoopMultigraph
import Theorems.Thm_Sabidussi_bracketRightHom_apply
import Theorems.Thm_Sabidussi_bracket_self
import Theorems.Thm_Sabidussi_tripleDifference_one
import Theorems.Thm_Sabidussi_tripleDifference_two
import Theorems.Thm_Sabidussi_tripleDifference_zero
attribute [local simp] Sabidussi.bracketRightHom_apply
attribute [local simp] Sabidussi.bracket_self
attribute [local simp] Sabidussi.tripleDifference_one
attribute [local simp] Sabidussi.tripleDifference_two
attribute [local simp] Sabidussi.tripleDifference_zero



set_option autoImplicit true
open Sabidussi
open scoped BigOperators
open Sabidussi.LoopMultigraph
variable {V E : Type*} [Fintype V] [Fintype E]
open Sabidussi.LoopMultigraph.EulerTour
variable [DecidableEq V] {G : LoopMultigraph V E} (T : G.EulerTour)
namespace Sabidussi.LoopMultigraph.EulerTour
theorem _root_.solution (v : V) :
    G.degree v = 2 * Fintype.card (T.Occurrence v) := by
  rw [degree, ← Fintype.card_congr (T.occurrenceSideEquivHalfEdgesAt v), Fintype.card_prod]
  simp [Nat.mul_comm]
end Sabidussi.LoopMultigraph.EulerTour
