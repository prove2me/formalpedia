-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.groupedTypeViolationCount_eq_typeViolationCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:36:11.822993+00:00
-- url     : https://prove2.me/submissions/e7ea8382-c8c0-44b6-8a62-375af242ba29

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Mathlib.Probability.Independence.Integration
import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_sum_sampleRowViolationIndicator_typeRows_eq_groupedCount
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_sum_sampleRowViolationIndicator_typeRows_eq

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    {r typeCount ell : Nat} [NeZero typeCount]
    (sample : Sample r)
    (typeShifts : Fin typeCount → Fin (ell - 1))
    (τ : Fin typeCount)
    (y z : Word (ZMod 2) (Fin (4 * r))) :
    groupedTypeViolationCount sample τ y z =
      TwistGraph.typeViolationCount
        (baseSample sample) (twistSample sample typeShifts)
        τ y z := by
  exact_mod_cast
    (sum_sampleRowViolationIndicator_typeRows_eq_groupedCount
      sample τ y z).symm.trans
      (sum_sampleRowViolationIndicator_typeRows_eq
        sample typeShifts τ y z)
end QEC.Coding.FiberBundle.RandomPartition
