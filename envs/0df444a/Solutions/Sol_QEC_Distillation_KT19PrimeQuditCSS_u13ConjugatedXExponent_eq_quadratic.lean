-- Prove2me | solution 1 for QEC.Distillation.KT19PrimeQuditCSS.u13ConjugatedXExponent_eq_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:43:03.436632+00:00
-- url     : https://prove2.me/submissions/43b80253-18da-4ed0-8166-9612017c3fd0

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
    u13ConjugatedXExponent p x = 3 * x ^ 2 + 3 * x + 1 := by
  unfold u13ConjugatedXExponent
  ring
end QEC.Distillation.KT19PrimeQuditCSS
