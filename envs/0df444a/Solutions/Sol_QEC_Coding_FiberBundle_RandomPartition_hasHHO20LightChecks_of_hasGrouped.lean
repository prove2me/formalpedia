-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.hasHHO20LightChecks_of_hasGrouped
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:37:52.748206+00:00
-- url     : https://prove2.me/submissions/0ee18248-e237-453b-bb9a-9b91c604059b

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Mathlib.Probability.Independence.Integration
import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_groupedTypeViolationCount_eq_typeViolationCount

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    {r Delta typeCount ell : Nat} [NeZero typeCount]
    (sample : Sample r)
    (typeShifts : Fin typeCount → Fin (ell - 1))
    (hGrouped :
      HasGroupedHHO20LightChecks
        (r := r) (typeCount := typeCount) Delta sample) :
    TwistGraph.HasHHO20LightChecks Delta
      (baseSample sample) (twistSample sample typeShifts) := by
  intro τ y z hy hz
  rw [← groupedTypeViolationCount_eq_typeViolationCount
    sample typeShifts τ y z]
  exact hGrouped τ y z hy hz
end QEC.Coding.FiberBundle.RandomPartition
