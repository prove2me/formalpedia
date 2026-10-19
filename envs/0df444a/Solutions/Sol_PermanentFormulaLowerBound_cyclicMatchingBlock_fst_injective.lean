-- Prove2me | solution 1 for PermanentFormulaLowerBound.cyclicMatchingBlock_fst_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/03b24b87-3166-40e1-8225-78e7ef49ac77

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
      (fun x : ↥(cyclicMatchingBlock hk t j) => x.1.1) := by
  classical
  letI : NeZero n :=
    ⟨Nat.ne_of_gt ((Nat.zero_le (t : ℕ)).trans_lt t.isLt)⟩
  intro x y hrow
  change x.1.1 = y.1.1 at hrow
  obtain ⟨r, _, hr⟩ := Finset.mem_image.mp x.property
  obtain ⟨r', _, hr'⟩ := Finset.mem_image.mp y.property
  have hxgraph : x.1.2 = x.1.1 + t := by
    rw [← hr]
  have hygraph : y.1.2 = y.1.1 + t := by
    rw [← hr']
  apply Subtype.ext
  apply Prod.ext
  · exact hrow
  · rw [hxgraph, hygraph, hrow]
end PermanentFormulaLowerBound
