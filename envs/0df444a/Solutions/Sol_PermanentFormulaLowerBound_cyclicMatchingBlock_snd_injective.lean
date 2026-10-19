-- Prove2me | solution 1 for PermanentFormulaLowerBound.cyclicMatchingBlock_snd_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/a8b7a084-cf36-40ce-93f5-f3876ac3e28e

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution {n k : ℕ}
    (hk : 0 < k) (t : Fin n) (j : Fin (n / k)) :
    Function.Injective
      (fun x : ↥(cyclicMatchingBlock hk t j) => x.1.2) := by
  classical
  letI : NeZero n :=
    ⟨Nat.ne_of_gt ((Nat.zero_le (t : ℕ)).trans_lt t.isLt)⟩
  intro x y hcol
  change x.1.2 = y.1.2 at hcol
  obtain ⟨r, _, hr⟩ := Finset.mem_image.mp x.property
  obtain ⟨r', _, hr'⟩ := Finset.mem_image.mp y.property
  have hxgraph : x.1.2 = x.1.1 + t := by
    rw [← hr]
  have hygraph : y.1.2 = y.1.1 + t := by
    rw [← hr']
  have hrow : x.1.1 = y.1.1 := by
    apply add_right_cancel (b := t)
    rw [← hxgraph, ← hygraph]
    exact hcol
  apply Subtype.ext
  exact Prod.ext hrow hcol
end PermanentFormulaLowerBound
