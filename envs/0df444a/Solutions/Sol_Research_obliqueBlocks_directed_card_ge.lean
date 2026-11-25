-- Prove2me | solution 1 for Research.obliqueBlocks_directed_card_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:18:48.375953+00:00
-- url     : https://prove2.me/submissions/d90eeb1c-1d50-4dc0-adc7-c2eccf419e6d

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
public import Theorems.Thm_Research_RadiusSixPairType_card_eq
public import Theorems.Thm_Research_shellSixBlockIncidence_card

set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder
namespace Research
theorem _root_.solution (m : ℕ) :
    m * 16786618 ≤ (radiusSixDirectedPairs (obliqueBlocks m)).card := by
  calc
    m * 16786618 = Fintype.card (ShellSixBlockIncidence m) :=
      (shellSixBlockIncidence_card m).symm
    _ ≤ Fintype.card (RadiusSixPairType (obliqueBlocks m)) :=
      Fintype.card_le_of_embedding (shellSixBlockIncidenceToDirected m)
    _ = (radiusSixDirectedPairs (obliqueBlocks m)).card :=
      RadiusSixPairType_card_eq (obliqueBlocks m)
end Research
