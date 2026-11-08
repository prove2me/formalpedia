-- Prove2me | solution 1 for QEC.Coding.FiberBundle.HHO20DistanceBalancing.initial_dimension_square_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:30:07.501453+00:00
-- url     : https://prove2.me/submissions/7c51366e-8d2a-4ab8-934c-a2ebe96167d5

import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_DistanceBalancingLocality
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_InitialLocality
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Asymptotics
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_hho20_baseScale_le_two_fiberCells


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.HHO20DistanceBalancing
open QEC.Coding
universe u
namespace QEC.Coding.FiberBundle.HHO20DistanceBalancing
theorem _root_.solution (s : Nat) (hs : 200 ≤ s) :
    initialBlocklengthAt s ≤ 7 * initialDimensionAt s ^ 2 ∧
    7 * initialDimensionAt s ^ 2 ≤ 2 * initialBlocklengthAt s := by
  have hLower := Nat.le_of_lt
    (RandomPartition.hho20_fiberCells_lt_baseScale s (by omega))
  have hUpper := RandomPartition.hho20_baseScale_le_two_fiberCells s hs
  unfold initialBlocklengthAt initialDimensionAt
  constructor <;> nlinarith
end QEC.Coding.FiberBundle.HHO20DistanceBalancing
