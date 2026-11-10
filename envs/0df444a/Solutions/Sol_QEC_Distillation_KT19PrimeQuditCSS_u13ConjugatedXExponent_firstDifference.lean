-- Prove2me | solution 1 for QEC.Distillation.KT19PrimeQuditCSS.u13ConjugatedXExponent_firstDifference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:43:05.797048+00:00
-- url     : https://prove2.me/submissions/e1faaaff-1a31-41a1-bfaf-03a5b53149e8

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
    u13ConjugatedXExponent p (x + 1) - u13ConjugatedXExponent p x = 6 * x + 6 := by
  unfold u13ConjugatedXExponent
  ring
end QEC.Distillation.KT19PrimeQuditCSS
