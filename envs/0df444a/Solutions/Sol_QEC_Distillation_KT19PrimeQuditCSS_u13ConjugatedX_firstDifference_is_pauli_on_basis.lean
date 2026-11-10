-- Prove2me | solution 1 for QEC.Distillation.KT19PrimeQuditCSS.u13ConjugatedX_firstDifference_is_pauli_on_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:46:53.941195+00:00
-- url     : https://prove2.me/submissions/d0abb677-8307-4b4a-9990-8c3c8bbe9ee5

import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_zPowerTransport_apply_basis
import Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_u13ConjugatedX_firstDifference_is_pauli

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.KT19PrimeQuditCSS
open Semantics
open scoped BigOperators
universe u
attribute [local instance] QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype
namespace QEC.Distillation.KT19PrimeQuditCSS
theorem _root_.solution (p : Nat) [NeZero p]
    (x : ZMod p) :
    phase p (u13ConjugatedXExponent p (x + 1) - u13ConjugatedXExponent p x) •
        quditBasisKet p x =
      phase p 6 • zPowerTransport p 6 (quditBasisKet p x) := by
  rw [zPowerTransport_apply_basis, smul_smul,
    u13ConjugatedX_firstDifference_is_pauli]
end QEC.Distillation.KT19PrimeQuditCSS
