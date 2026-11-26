-- Prove2me | solution 1 for TunnellMap.branch1_paper_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:52:57.056196+00:00
-- url     : https://prove2.me/submissions/0ed8d443-561b-47b7-88a4-4335f822fd29

import Definitions.Def_TunnellMap_Basic
import Definitions.Def_TunnellMap_QuarterTurns
import Theorems.Thm_TunnellMap_evenEquiv_apply
import Theorems.Thm_TunnellMap_evenEquiv_symm_apply
attribute [local simp] TunnellMap.evenEquiv_apply
attribute [local simp] TunnellMap.evenEquiv_symm_apply



set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ} (p : DirectDomain1 n) :
    2 * (branch1Equiv n p).rep.1.x =
        p.rep.1.x + 2 * p.rep.1.z - p.rep.1.y ∧
      (branch1Equiv n p).rep.1.y = p.rep.1.x - 2 * p.rep.1.z ∧
      8 * (branch1Equiv n p).rep.1.z =
        p.rep.1.x + 2 * p.rep.1.z + p.rep.1.y := by
  dsimp [branch1Equiv, branch1To]
  constructor
  · nlinarith [p.equation]
  · constructor
    · rfl
    · nlinarith [p.equation]
end TunnellMap
