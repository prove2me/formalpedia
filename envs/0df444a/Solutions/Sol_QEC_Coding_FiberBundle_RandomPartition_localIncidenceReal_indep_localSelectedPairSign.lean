-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.localIncidenceReal_indep_localSelectedPairSign
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:31:15.207249+00:00
-- url     : https://prove2.me/submissions/7685d342-cf1a-489e-a810-2dd8d24e2a43

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Mathlib.Probability.Independence.Integration
import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_localDistribution_coordinate_iIndepFun

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (b : Fin (4 * r)) :
    ProbabilityTheory.IndepFun
      localIncidenceReal
      (localSelectedPairSign y z b)
      (localDistribution r Delta hDelta).toMeasure := by
  exact
    (((localDistribution_coordinate_iIndepFun
      r Delta hDelta).indepFun
      (by decide : false ≠ true)).comp
      (Measurable.of_discrete :
        Measurable (fun incidence : Bool =>
          cond incidence (1 : Real) 0))
      (Measurable.of_discrete :
        Measurable (fun tail : Bool =>
          if tail then
            RandomBase.paritySign (y b)
          else
            RandomBase.paritySign (z b))))
end QEC.Coding.FiberBundle.RandomPartition
