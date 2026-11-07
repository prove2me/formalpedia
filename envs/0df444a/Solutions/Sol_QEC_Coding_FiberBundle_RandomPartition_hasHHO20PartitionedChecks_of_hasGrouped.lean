-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.hasHHO20PartitionedChecks_of_hasGrouped
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:40:21.754708+00:00
-- url     : https://prove2.me/submissions/3583d317-1c48-4ae4-9eea-adbcf944f696

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Mathlib.Probability.Independence.Integration
import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_hasHHO20LightChecks_of_hasGrouped

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    {r Delta typeCount ell : Nat} [NeZero typeCount]
    (sample : Sample r)
    (typeShifts : Fin typeCount → Fin (ell - 1))
    (h :
      HasGroupedHHO20PartitionedChecks
        Delta typeShifts sample) :
    TwistGraph.HasHHO20PartitionedChecks Delta
      (baseSample sample) (twistSample sample typeShifts) := by
  exact
    ⟨hasHHO20LightChecks_of_hasGrouped
        sample typeShifts h.1,
      h.2⟩
end QEC.Coding.FiberBundle.RandomPartition
