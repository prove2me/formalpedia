-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.typeTwist_twistSample
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:19:02.32611+00:00
-- url     : https://prove2.me/submissions/f2c7fd9c-0413-492f-aeab-d1bccbb4248c

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Mathlib.Probability.Independence.Integration
import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    {r typeCount ell : Nat}
    (sample : Sample r)
    (typeShifts : Fin typeCount → Fin (ell - 1))
    (τ : Fin typeCount) :
    RandomTwist.typeTwist (twistSample sample typeShifts) τ =
      typeShifts τ := by
  rfl
end QEC.Coding.FiberBundle.RandomPartition
