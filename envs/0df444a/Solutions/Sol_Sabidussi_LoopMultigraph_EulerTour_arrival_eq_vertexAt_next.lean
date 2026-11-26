-- Prove2me | solution 1 for Sabidussi.LoopMultigraph.EulerTour.arrival_eq_vertexAt_next
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:16:00.353519+00:00
-- url     : https://prove2.me/submissions/b54e6e3f-777b-49ea-a412-89ecf114be0c

import Definitions.Def_Sabidussi_Color
import Definitions.Def_Sabidussi_Statement
import Mathlib.Data.Fin.Rev
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finite.Set
import Mathlib.Data.Fintype.Sets
import Definitions.Def_Sabidussi_LoopMultigraph

set_option autoImplicit true
open Sabidussi
open scoped BigOperators
open Sabidussi.LoopMultigraph
variable {V E : Type*} [Fintype V] [Fintype E]
open Sabidussi.LoopMultigraph.EulerTour
variable [DecidableEq V] {G : LoopMultigraph V E} (T : G.EulerTour)
namespace Sabidussi.LoopMultigraph.EulerTour
theorem _root_.solution (i : T.Pos) : T.arrivalAt i = T.vertexAt (T.next i) := by
  exact T.continuous i
end Sabidussi.LoopMultigraph.EulerTour
