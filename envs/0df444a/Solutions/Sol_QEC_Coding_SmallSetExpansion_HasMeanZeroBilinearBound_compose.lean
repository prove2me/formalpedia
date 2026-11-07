-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.HasMeanZeroBilinearBound.compose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:48:08.712565+00:00
-- url     : https://prove2.me/submissions/e5e125c6-0514-4a8e-9db1-1a6ee4bb2f85

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSpectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionOperators
import Theorems.Thm_QEC_Coding_SmallSetExpansion_HasMeanZeroOperatorBound_toBilinearBound
import Theorems.Thm_QEC_Coding_SmallSetExpansion_hasMeanZeroBilinearBound_iff_operatorBound


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u} [Fintype V]
namespace QEC.Coding.SmallSetExpansion
namespace HasMeanZeroBilinearBound
theorem _root_.solution
    {M N : WeightedGraph V} {lambda mu : ℝ} (degreeM degreeN : Nat)
    (hSymmetricM : IsSymmetric M) (hRegularM : IsRegular M degreeM)
    (hSymmetricN : IsSymmetric N) (hRegularN : IsRegular N degreeN)
    (hLambda : 0 ≤ lambda) (hMu : 0 ≤ mu)
    (hM : HasMeanZeroBilinearBound M lambda) (hN : HasMeanZeroBilinearBound N mu) :
    HasMeanZeroBilinearBound (compose M N) (lambda * mu) := by
  apply HasMeanZeroOperatorBound.toBilinearBound (mul_nonneg hLambda hMu)
  exact HasMeanZeroOperatorBound.compose degreeN hSymmetricN hRegularN
    ((hasMeanZeroBilinearBound_iff_operatorBound hSymmetricM hRegularM hLambda).mp hM)
    ((hasMeanZeroBilinearBound_iff_operatorBound hSymmetricN hRegularN hMu).mp hN)
end HasMeanZeroBilinearBound
end QEC.Coding.SmallSetExpansion
