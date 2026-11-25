-- Prove2me | solution 1 for StableMarriageF6Public.totalAntichains_le_48
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:16:26.246857+00:00
-- url     : https://prove2.me/submissions/83d9ca4c-068b-4104-9dfb-ef66c1bbd669

import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
import Definitions.Def_StableMarriageF6_PalomarSolution
import Theorems.Thm_F6ConvexWindow_totalAntichains_le_48


set_option autoImplicit true
noncomputable section
open StableMarriageF6Public
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace StableMarriageF6Public
theorem _root_.solution
    (hw : widthLE (V := V) 3)
    (hci : ci2 (V := V))
    (hn : Fintype.card V ≤ 15) :
    totalNumberOfAntichains (V := V) ≤ 48 := by
  change F6ConvexWindow.WidthLE (V := V) 3 at hw
  change F6ConvexWindow.CI2 (V := V) at hci
  change F6ConvexWindow.totalAntichains (V := V) ≤ 48
  exact F6ConvexWindow.totalAntichains_le_48 hw hci hn
end StableMarriageF6Public
