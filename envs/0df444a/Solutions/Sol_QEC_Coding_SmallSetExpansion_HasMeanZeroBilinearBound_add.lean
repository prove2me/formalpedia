-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.HasMeanZeroBilinearBound.add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:57:18.694737+00:00
-- url     : https://prove2.me/submissions/30a5d27e-f1a6-4312-9f52-12d761fdfc19

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSpectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionOperators
import Theorems.Thm_QEC_Coding_SmallSetExpansion_adjacencyPairing_add
import Theorems.Thm_QEC_Coding_SmallSetExpansion_IsSmallSetEdgeExpanding_add


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u} [Fintype V]
namespace QEC.Coding.SmallSetExpansion
namespace HasMeanZeroBilinearBound
theorem _root_.solution
    {M N : WeightedGraph V} {lambda mu : ℝ}
    (hM : HasMeanZeroBilinearBound M lambda) (hN : HasMeanZeroBilinearBound N mu) :
    HasMeanZeroBilinearBound (add M N) (lambda + mu) := by
  intro f g hf hg
  rw [adjacencyPairing_add]
  calc
    _ ≤ |adjacencyPairing M f g| + |adjacencyPairing N f g| := abs_add_le _ _
    _ ≤ lambda * Real.sqrt ((∑ v, (f v) ^ 2) * ∑ v, (g v) ^ 2) +
        mu * Real.sqrt ((∑ v, (f v) ^ 2) * ∑ v, (g v) ^ 2) := add_le_add (hM f g hf hg) (hN f g hf hg)
    _ = _ := by ring
end HasMeanZeroBilinearBound
end QEC.Coding.SmallSetExpansion
