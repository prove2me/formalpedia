-- Prove2me | solution 1 for Research.obliquePatch_directed_card_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:12:55.255871+00:00
-- url     : https://prove2.me/submissions/64d5c028-f587-4d93-86b8-1b37fb7a52f1

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
public import Theorems.Thm_Research_shellSixIncidence_card
public import Theorems.Thm_Research_RadiusSixPairType_card_eq

set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder
namespace Research
theorem _root_.solution :
    16786618 ≤ (radiusSixDirectedPairs obliquePoint).card := by
  calc
    16786618 = Fintype.card ShellSixIncidence := shellSixIncidence_card.symm
    _ ≤ Fintype.card (RadiusSixPairType obliquePoint) :=
      Fintype.card_le_of_embedding shellSixIncidenceToDirected
    _ = (radiusSixDirectedPairs obliquePoint).card :=
      RadiusSixPairType_card_eq obliquePoint
end Research
