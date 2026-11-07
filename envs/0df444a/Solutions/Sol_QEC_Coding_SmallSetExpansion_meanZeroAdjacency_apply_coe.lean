-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.meanZeroAdjacency_apply_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:36:19.307727+00:00
-- url     : https://prove2.me/submissions/16ad7ade-f356-4723-a8c2-d74791061eed

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
    (hSymmetric : IsSymmetric M) (hRegular : IsRegular M degree)
    (f : meanZeroEuclideanSubspace (V := V)) (v : V) :
    (meanZeroAdjacency M degree hSymmetric hRegular f :
      EuclideanSpace ℂ V) v =
      complexWeightedNeighborSum M (fun u => f.1 u) v := rfl
end QEC.Coding.SmallSetExpansion
