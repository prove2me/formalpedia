-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingBinaryDegree_bitSubset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/e7a43054-92b0-434e-8292-bbb1dd9d214c

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_matchingBitSubset_map_val

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution (ell d : ℕ) (hd : d < 2 ^ ell) :
    matchingBinaryDegree (matchingBitSubset ell d) = d := by
  classical
  unfold matchingBinaryDegree
  calc
    (∑ u ∈ matchingBitSubset ell d, 2 ^ (u : ℕ)) =
        ∑ a ∈ (matchingBitSubset ell d).map Fin.valEmbedding, 2 ^ a :=
          (Finset.sum_map (matchingBitSubset ell d)
            Fin.valEmbedding (fun a : ℕ => 2 ^ a)).symm
    _ = ∑ a ∈ d.bitIndices.toFinset, 2 ^ a := by
      rw [matchingBitSubset_map_val ell d hd]
    _ = (d.bitIndices.map (fun a => 2 ^ a)).sum :=
      List.sum_toFinset (fun a : ℕ => 2 ^ a) Nat.bitIndices_nodup
    _ = d := Nat.sum_map_two_pow_bitIndices d
end PermanentFormulaLowerBound
