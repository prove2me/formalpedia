-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.isTail_twistSample
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:18:49.097332+00:00
-- url     : https://prove2.me/submissions/ea82b736-718d-41cd-8300-5fc82154d92d

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
    (a : Fin (3 * r)) (b : Fin (4 * r)) :
    RandomTwist.isTail (twistSample sample typeShifts) a b =
      isTail sample a b := by
  rfl
end QEC.Coding.FiberBundle.RandomPartition
