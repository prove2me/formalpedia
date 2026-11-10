-- Prove2me | solution 1 for QEC.Distillation.KT19P11ReedSolomonCubicBridge.p11_physicalU13_implements_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T13:02:14.505053+00:00
-- url     : https://prove2.me/submissions/96323196-b3ea-4ad9-9cc6-335c98a429be

import Definitions.Def_QEC_Coding_ReedSolomon_Punctured
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_P11CubicBridge
import Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_CubicRowFamily_physicalU13_implements_inverseLogicalU13

section
noncomputable section
namespace QEC.Distillation.KT19P11ReedSolomonCubicBridge
open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open QEC.Distillation.KT19PrimeQuditCSS
open scoped BigOperators
attribute [local instance] p11Prime p11NeZero p11PrimeQuditRegisterLabelFintype
private theorem p11_primeAtLeastFive : PrimeAtLeastFive 11 := by
  constructor <;> norm_num
end QEC.Distillation.KT19P11ReedSolomonCubicBridge
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.KT19P11ReedSolomonCubicBridge
open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open QEC.Distillation.KT19PrimeQuditCSS
open scoped BigOperators
attribute [local instance] QEC.Distillation.KT19P11ReedSolomonCubicBridge.p11Prime
attribute [local instance] QEC.Distillation.KT19P11ReedSolomonCubicBridge.p11NeZero
attribute [local instance] QEC.Distillation.KT19P11ReedSolomonCubicBridge.p11PrimeQuditRegisterLabelFintype
attribute [local instance] p11Prime p11NeZero p11PrimeQuditRegisterLabelFintype
namespace QEC.Distillation.KT19P11ReedSolomonCubicBridge
theorem _root_.solution :
    p11CubicRowFamily.encodedCode.ImplementsLogicalGate
      p11CubicRowFamily.physicalU13 p11CubicRowFamily.logicalInverseU13 :=
  CubicRowFamily.physicalU13_implements_inverseLogicalU13 p11CubicRowFamily
    p11_primeAtLeastFive
end QEC.Distillation.KT19P11ReedSolomonCubicBridge
