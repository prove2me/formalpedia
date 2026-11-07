-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.centeredAdjacencyEuclidean_apply_of_sum_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:46:38.418663+00:00
-- url     : https://prove2.me/submissions/fd1f65f6-f0cf-4b67-b910-dd382e7a284d

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSpectrum

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
namespace QEC.Coding.SmallSetExpansion
theorem _root_.solution
    [Fintype V]
    (M : WeightedGraph V) (degree : Nat)
    (f : EuclideanSpace ℂ V) (hf : (∑ v, f v) = 0) :
    centeredAdjacencyEuclidean M degree f =
      complexAdjacencyEuclidean M f := by
  simp [centeredAdjacencyEuclidean, hf]
end QEC.Coding.SmallSetExpansion
