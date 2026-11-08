-- Prove2me | solution 1 for QEC.Coding.FiberBundle.HHO20DistanceBalancing.finrank_middleHomology_le_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:30:17.445318+00:00
-- url     : https://prove2.me/submissions/7125cc7f-6e17-460a-b478-53348b061eba

import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_DistanceBalancingLocality
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_InitialLocality
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Asymptotics
import Theorems.Thm_QEC_Coding_LinearCode_dimension_le_length


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.HHO20DistanceBalancing
open QEC.Coding
universe u
namespace QEC.Coding.FiberBundle.HHO20DistanceBalancing
theorem _root_.solution
    {zero one two : Type u} [Fintype zero] [Fintype one] [Fintype two]
    (X : ChainComplexData (ZMod 2)
      (Word (ZMod 2) zero) (Word (ZMod 2) one) (Word (ZMod 2) two)) :
    Module.finrank (ZMod 2) X.middleHomology ≤ Fintype.card one := by
  calc
    Module.finrank (ZMod 2) X.middleHomology ≤
        Module.finrank (ZMod 2) X.middleCycleCode.carrier :=
      Submodule.finrank_quotient_le X.middleBoundaryInCycles
    _ = Dimension X.middleCycleCode := rfl
    _ ≤ Length (ZMod 2) one := X.middleCycleCode.dimension_le_length
    _ = Fintype.card one := rfl
end QEC.Coding.FiberBundle.HHO20DistanceBalancing
