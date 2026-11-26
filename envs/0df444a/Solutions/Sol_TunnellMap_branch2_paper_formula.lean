-- Prove2me | solution 1 for TunnellMap.branch2_paper_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:53:16.447718+00:00
-- url     : https://prove2.me/submissions/ff8aa4db-ac70-475a-8f98-7cd10ab5d5b0

import Definitions.Def_TunnellMap_Basic
import Definitions.Def_TunnellMap_QuarterTurns
import Theorems.Thm_TunnellMap_evenEquiv_apply
import Theorems.Thm_TunnellMap_evenEquiv_symm_apply
attribute [local simp] TunnellMap.evenEquiv_apply
attribute [local simp] TunnellMap.evenEquiv_symm_apply



set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ} (p : DirectDomain2 n) :
    2 * (branch2Equiv n p).rep.1.x =
        p.rep.1.x - 2 * p.rep.1.z + p.rep.1.y ∧
      (branch2Equiv n p).rep.1.y = -p.rep.1.x - 2 * p.rep.1.z ∧
      8 * (branch2Equiv n p).rep.1.z =
        p.rep.1.y - p.rep.1.x + 2 * p.rep.1.z := by
  dsimp [branch2Equiv, branch2To]
  constructor
  · nlinarith [p.equation]
  · constructor
    · rfl
    · nlinarith [p.equation]
end TunnellMap
