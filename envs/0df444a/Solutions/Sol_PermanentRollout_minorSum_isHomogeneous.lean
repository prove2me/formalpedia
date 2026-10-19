-- Prove2me | solution 1 for PermanentRollout.minorSum_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/1810efbc-cfba-4bb5-be91-00031c9595ea

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution (t s d : ℕ) :
    (minorSum t s d).IsHomogeneous d := by
  classical
  unfold minorSum
  apply MvPolynomial.IsHomogeneous.sum
  intro rows hrows
  apply MvPolynomial.IsHomogeneous.sum
  intro columns _
  apply MvPolynomial.IsHomogeneous.sum
  intro matching _
  have hcard : rows.card = d := (Finset.mem_powersetCard.mp hrows).2
  convert MvPolynomial.IsHomogeneous.prod Finset.univ
    (fun row : rows =>
      MvPolynomial.X (row.val, (matching row).val) :
        rows → MvPolynomial (Fin t × Fin s) ℂ)
    (fun _ => 1)
    (fun row _ => MvPolynomial.isHomogeneous_X ℂ (row.val, (matching row).val)) using 1
  simp [hcard]
end PermanentRollout
