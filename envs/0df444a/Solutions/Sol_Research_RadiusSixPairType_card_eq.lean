-- Prove2me | solution 1 for Research.RadiusSixPairType_card_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:52:52.256438+00:00
-- url     : https://prove2.me/submissions/e1af78d8-9740-4c1c-94d1-d3509cb21583

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
public import Theorems.Thm_Research_mem_radiusSixDirectedPairs_iff

set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder
namespace Research
theorem _root_.solution {α : Type*} [Fintype α]
    [DecidableEq α] (p : α → ℝ × ℝ) :
    Fintype.card (RadiusSixPairType p) = (radiusSixDirectedPairs p).card := by
  classical
  let e : RadiusSixPairType p ≃ {q // q ∈ radiusSixDirectedPairs p} :=
    Equiv.subtypeEquivRight fun q => (mem_radiusSixDirectedPairs_iff p q).symm
  calc
    Fintype.card (RadiusSixPairType p) =
        Fintype.card {q // q ∈ radiusSixDirectedPairs p} :=
      Fintype.card_congr e
    _ = (radiusSixDirectedPairs p).card :=
      Fintype.card_coe (radiusSixDirectedPairs p)
end Research
