-- Prove2me | solution 1 for QEC.Distillation.KT19PrimeQuditCSS.phase_fintype_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:44:36.917356+00:00
-- url     : https://prove2.me/submissions/1c0ede4d-926a-4c1b-8308-8e7b95420724

import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_phase_finset_sum
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.KT19PrimeQuditCSS
open Semantics
open scoped BigOperators
universe u
attribute [local instance] QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype
namespace QEC.Distillation.KT19PrimeQuditCSS
theorem _root_.solution (p : Nat) [NeZero p] {Index : Type u} [Fintype Index]
    (f : Index → ZMod p) :
    (∏ index : Index, phase p (f index)) = phase p (∑ index : Index, f index) :=
  (phase_finset_sum p Finset.univ f).symm
end QEC.Distillation.KT19PrimeQuditCSS
