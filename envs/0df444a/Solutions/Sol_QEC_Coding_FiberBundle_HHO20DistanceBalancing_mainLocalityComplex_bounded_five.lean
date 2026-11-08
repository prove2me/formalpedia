-- Prove2me | solution 1 for QEC.Coding.FiberBundle.HHO20DistanceBalancing.mainLocalityComplex_bounded_five
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:24:24.937722+00:00
-- url     : https://prove2.me/submissions/9a71a788-948a-489a-9b82-7b73e6efb1c5

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Locality
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_DistanceBalancing
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_DistanceBalancingLocality
import Theorems.Thm_QEC_Coding_DistanceBalancing_boundedLocality_of_canonical_boundary_bounds
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_HammingWeight_boundary2_weightReduced_randomFiberBundleData_canonical_le_five
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_HammingWeight_transpose_boundary1_weightReduced_randomFiberBundleData_canonical_le_five
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_chainComplexBoundaryIncidence_weightReduced_randomFiberBundleData_variableSupport_le_five


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.HHO20DistanceBalancing
open QEC.Coding
namespace QEC.Coding.FiberBundle.HHO20DistanceBalancing
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :
    BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence
        (mainLocalityComplex baseSample twistSample)).localityProfile 5 := by
  rw [← max_self 5]
  apply DistanceBalancing.boundedLocality_of_canonical_boundary_bounds
    (mainLocalityComplex baseSample twistSample)
      (checkBound := 5) (variableBound := 5)
  · intro c0
    change MainCZero baseSample twistSample at c0
    change HammingWeight
      (wordLinearMapTranspose
        (boundary1 (weightReducedData
          (RandomTwist.fiberBundleData baseSample twistSample)))
        (canonicalBasisWord (F := ZMod 2) c0)) ≤ 5
    rcases c0 with ⟨q, i⟩
    exact
      RandomBase.HammingWeight_transpose_boundary1_weightReduced_randomFiberBundleData_canonical_le_five
        baseSample twistSample q i
  · intro c2
    change MainCTwo baseSample twistSample at c2
    change HammingWeight
      (boundary2 (weightReducedData
        (RandomTwist.fiberBundleData baseSample twistSample))
        (canonicalBasisWord (F := ZMod 2) c2)) ≤ 5
    rcases c2 with ⟨b, j⟩
    exact
      RandomBase.HammingWeight_boundary2_weightReduced_randomFiberBundleData_canonical_le_five
        baseSample twistSample b j
  · intro q
    change MainQubit baseSample twistSample at q
    change ((QEC.QLDPC.chainComplexBoundaryIncidence
      (chainComplex (weightReducedData
        (RandomTwist.fiberBundleData baseSample twistSample)))).variableSupport q).card ≤ 5
    exact
      RandomBase.chainComplexBoundaryIncidence_weightReduced_randomFiberBundleData_variableSupport_le_five
        baseSample twistSample q
end QEC.Coding.FiberBundle.HHO20DistanceBalancing
