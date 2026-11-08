-- Prove2me | solution 1 for QEC.Coding.FiberBundle.HHO20DistanceBalancing.initialZDistanceScaleAt_le_source
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:30:05.829948+00:00
-- url     : https://prove2.me/submissions/e28fb038-20d9-45d3-b7ac-b9b636241163

import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_DistanceBalancingLocality
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_InitialLocality
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Asymptotics

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.HHO20DistanceBalancing
open QEC.Coding
universe u
namespace QEC.Coding.FiberBundle.HHO20DistanceBalancing
theorem _root_.solution
    (s : Nat) (hs : 200 ≤ s) :
    initialZDistanceScaleAt s ≤
      (RandomPartition.hho20FiberLength s *
        (4 * RandomPartition.hho20BaseScale s)) /
          (5000 * RandomPartition.hho20DegreeScale s) := by
  have hBase := Nat.le_of_lt
    (RandomPartition.hho20_fiberCells_lt_baseScale s (by omega))
  unfold initialZDistanceScaleAt
  apply Nat.div_le_div_right
  calc
    RandomPartition.hho20FiberLength s ^ 3 =
        RandomPartition.hho20FiberLength s *
          RandomPartition.hho20FiberLength s ^ 2 := by ring
    _ ≤ RandomPartition.hho20FiberLength s *
          RandomPartition.hho20BaseScale s :=
      Nat.mul_le_mul_left _ hBase
    _ ≤ RandomPartition.hho20FiberLength s *
          (4 * RandomPartition.hho20BaseScale s) := by
      apply Nat.mul_le_mul_left
      omega
end QEC.Coding.FiberBundle.HHO20DistanceBalancing
