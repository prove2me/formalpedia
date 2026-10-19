-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingBitSubset_map_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/f3c7f8eb-8a05-4051-8adc-c039e3581615

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution (ell d : ℕ) (hd : d < 2 ^ ell) :
    (matchingBitSubset ell d).map Fin.valEmbedding =
      d.bitIndices.toFinset := by
  classical
  ext a
  constructor
  · intro ha
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp ha
    have hbit : (u : ℕ) ∈ d.bitIndices :=
      (Finset.mem_filter.mp hu).2
    simpa using hbit
  · intro ha
    have hbit : a ∈ d.bitIndices := by simpa using ha
    have hlt : a < ell := by
      apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
      exact (Nat.two_pow_le_of_mem_bitIndices hbit).trans_lt hd
    refine Finset.mem_map.mpr ⟨⟨a, hlt⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbit⟩
end PermanentFormulaLowerBound
