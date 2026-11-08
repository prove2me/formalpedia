-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.weightReducedClassical_columnWeight_le_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:38:16.202188+00:00
-- url     : https://prove2.me/submissions/be233cce-42c2-4cc8-afda-1c232aa3c856

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Definitions.Def_QEC_Coding_FiberBundle_ClassicalLDPCBalance
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_HammingWeight_boundary_single_le_three


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open QEC.Coding
universe u v w
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    {r : Nat} (sample : Sample r)
    (b : ClassicalWeightReduction.WeightReducedBit
      (incidenceRelation sample)) :
    HammingWeight
      (ClassicalWeightReduction.boundary (F := ZMod 2)
        (incidenceRelation sample) (Pi.single b 1)) ≤ 3 :=
  ClassicalWeightReduction.HammingWeight_boundary_single_le_three
    (F := ZMod 2) (incidenceRelation sample) b
end QEC.Coding.FiberBundle.RandomBase
