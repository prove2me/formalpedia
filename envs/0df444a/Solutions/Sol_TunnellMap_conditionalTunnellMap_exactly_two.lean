-- Prove2me | solution 1 for TunnellMap.conditionalTunnellMap_exactly_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:57:29.145313+00:00
-- url     : https://prove2.me/submissions/c5fcc9dd-e5f5-457a-ac8f-463dc885c625

import Definitions.Def_TunnellMap_Basic
import Definitions.Def_TunnellMap_Assembly
import Theorems.Thm_TunnellMap_assemble_exactly_two

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ}
    (odd : BOddRep n ≃ ARep n) (a : ARep n) :
    ∃ x₁ x₂,
      x₁ ≠ x₂ ∧
      conditionalTunnellMap odd x₁ = a ∧
      conditionalTunnellMap odd x₂ = a ∧
      ∀ x, conditionalTunnellMap odd x = a ↔ x = x₁ ∨ x = x₂ :=
  assemble_exactly_two (evenEquiv n) odd a
end TunnellMap
