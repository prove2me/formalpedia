-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.HasMeanZeroComplexOperatorBound.toReal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:36:57.801838+00:00
-- url     : https://prove2.me/submissions/973f5569-d050-4d94-9bf6-0509c55a321d

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSpectrum

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
namespace QEC.Coding.SmallSetExpansion
namespace HasMeanZeroComplexOperatorBound
theorem _root_.solution
    [Fintype V]
    {M : WeightedGraph V} {spectral : ℝ}
    (hComplex : HasMeanZeroComplexOperatorBound M spectral) :
    HasMeanZeroOperatorBound M spectral := by
  intro g hg
  have hMean : (∑ v, (g v : ℂ)) = 0 := by
    exact_mod_cast hg
  have hBound := hComplex (fun v => (g v : ℂ)) hMean
  simpa [complexWeightedNeighborSum_real, sq_abs] using hBound
end HasMeanZeroComplexOperatorBound
end QEC.Coding.SmallSetExpansion
