-- Prove2me | solution 1 for QEC.Distillation.KT19P11ReedSolomonCubicBridge.p11_rowCarrier_eq_dual_shortenedComplement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T13:04:27.506898+00:00
-- url     : https://prove2.me/submissions/62b63d5e-ee59-4cd8-ab87-0bfba4180697

import Definitions.Def_QEC_Coding_ReedSolomon_Punctured
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_P11CubicBridge
import Theorems.Thm_QEC_Distillation_KT19P11ReedSolomonCubicBridge_p11_rowCarrier_eq_puncturedReedSolomon
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_shortenedReedSolomonCode_dual_eq_punctured
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm


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
    p11RowCarrier = (shortenedReedSolomonCode 11 7 2).dual.carrier := by
  rw [p11_rowCarrier_eq_puncturedReedSolomon]
  symm
  exact shortenedReedSolomonCode_dual_eq_punctured 11 4 2 (by norm_num [Admissible])
end QEC.Distillation.KT19P11ReedSolomonCubicBridge
