-- Prove2me | solution 1 for QEC.Distillation.KT19PrimeQuditCSS.phase_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:44:46.89299+00:00
-- url     : https://prove2.me/submissions/0faca74a-ab61-42e1-a4c9-df1b48065815

import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.KT19PrimeQuditCSS
open Semantics
open scoped BigOperators
universe u
attribute [local instance] QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype
namespace QEC.Distillation.KT19PrimeQuditCSS
theorem _root_.solution (p : Nat) [NeZero p] (x : ZMod p) :
    phase p (-x) = (phase p x)⁻¹ :=
  (ZMod.stdAddChar (N := p)).map_neg_eq_inv x
end QEC.Distillation.KT19PrimeQuditCSS
