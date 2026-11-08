-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.weightReducedClassical_rowWeight_le_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:37:40.848785+00:00
-- url     : https://prove2.me/submissions/5bda931e-22dd-4292-a84d-ef00ecbe7c38

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Definitions.Def_QEC_Coding_FiberBundle_ClassicalLDPCBalance
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_HammingWeight_transpose_boundary_single_le_three


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open QEC.Coding
universe u v w
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    {r : Nat} (sample : Sample r)
    (q : ClassicalWeightReduction.WeightReducedCheck
      (incidenceRelation sample)) :
    HammingWeight
      (wordLinearMapTranspose
        (ClassicalWeightReduction.boundary (F := ZMod 2)
          (incidenceRelation sample))
        (Pi.single q 1)) ≤ 3 :=
  ClassicalWeightReduction.HammingWeight_transpose_boundary_single_le_three
    (F := ZMod 2) (incidenceRelation sample) q
end QEC.Coding.FiberBundle.RandomBase
