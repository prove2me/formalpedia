-- Prove2me | solution 1 for TunnellMap.branch3_paper_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:53:34.053407+00:00
-- url     : https://prove2.me/submissions/31bae03a-bebb-4748-84ac-5b519ec5d93b

import Definitions.Def_TunnellMap_Basic
import Definitions.Def_TunnellMap_QuarterTurns
import Theorems.Thm_TunnellMap_evenEquiv_apply
import Theorems.Thm_TunnellMap_evenEquiv_symm_apply
attribute [local simp] TunnellMap.evenEquiv_apply
attribute [local simp] TunnellMap.evenEquiv_symm_apply



set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ} (p : DirectDomain3 n) :
    (branch3Equiv n p).rep.1 =
      ⟨2 * p.rep.1.z, p.rep.1.y, -(p.rep.1.x / 4)⟩ := by
  apply Triple.ext <;> dsimp [branch3Equiv, branch3To]
  have hdiv : p.rep.1.x / 4 = p.quotient := by
    rw [p.equation]
    norm_num
  rw [hdiv]
end TunnellMap
