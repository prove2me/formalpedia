-- Prove2me | solution 1 for QEC.Distillation.KT19PrimeQuditCSS.cubicExponent_eq_cubicPairing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:43:20.247552+00:00
-- url     : https://prove2.me/submissions/a4610d8b-0924-45ea-a73c-d56a24d2e7fa

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
attribute [local instance] primeQuditRegisterLabelFintype
namespace QEC.Distillation.KT19PrimeQuditCSS
theorem _root_.solution (p : Nat) [NeZero p] {Site : Type u} [Fintype Site]
    (label : PrimeQuditRegisterLabel p Site) :
    cubicExponent p label = cubicPairing p label label label := by
  unfold cubicExponent cubicPairing
  apply Finset.sum_congr rfl
  intro site _
  ring
end QEC.Distillation.KT19PrimeQuditCSS
